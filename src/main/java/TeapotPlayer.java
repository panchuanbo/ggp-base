import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

import org.ggp.base.apps.player.Player;
import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.cache.CachedStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;

public class TeapotPlayer extends StateMachineGamer {

	// Convenience
	Player p;

	// Constants
	private final static int NTH_STEP_MOBILITY_LIMIT = 2;
	private final static int TIMEOUT_BUFFER = 2500; // 2500ms = 2.5s
	private final static int NUM_WEIGHTS = 3;

	// Stores the timeout (given timeout - buffer)
	long timeout;

	// Stores all the weights that we'll be using
	double[] weights = new double[NUM_WEIGHTS];

	// Stores the current limit for iterative deepening
	int limit = 0;

	// for debugging purposes, here's the limit
	int turn = 0;

	@Override
	public StateMachine getInitialStateMachine() {
		// TODO Auto-generated method stub
		return new CachedStateMachine(new ProverStateMachine());
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// TODO - Uncomment + Finish
		// Simulate games to learn more about what's happening/how to play
		// Want to find out what weight values to use

		this.turn = 0;

		StateMachine machine = getStateMachine();
		Role role = getRole();
		MachineState state = getCurrentState();

		for (Role r : machine.getRoles()) {
			if (r.equals(role)) System.out.println("My Focus: " + evalFuncFocus(r, state));
			else System.out.println("Opponent Focus: " + evalFuncFocus(r, state));
		}

		int ourMoveCount = 0, gamesSimulated = 0, gamesWeWon = 0;
		ArrayList<Double> values = new ArrayList<>(Arrays.asList(0.0, 0.0, 0.0, 0.0, 0.0, 0.0));;
		double ourMobility = 0, ourFocus = 0, ourGoal = 0;

		while (System.currentTimeMillis() < timeout - TIMEOUT_BUFFER) {
			if (machine.isTerminal(state)) { // done
				gamesSimulated++;
				int goal = machine.getGoal(state, role);
				boolean useGame = true;
				for (Role r : machine.getRoles()) {
					if (!r.equals(role) && machine.getGoal(state, r) >= goal) useGame = false;
				}
				if (useGame) {
					System.out.println("Our Score: " + goal + " | All Scores: " + machine.getGoals(state));
					System.out.println("Mobility: " + ourMobility/ourMoveCount + " | Focus: " + ourFocus/ourMoveCount + " | Goal: " + ourGoal/ourMoveCount);
					values.set(0, values.get(0) + ourMobility/ourMoveCount);
					values.set(1, values.get(1) + ourFocus/ourMoveCount);
					values.set(2, values.get(2) + ourGoal/ourMoveCount);
					gamesWeWon++;
				}

				machine = getStateMachine();
				role = getRole();
				state = getCurrentState();
				ourMobility = ourFocus = ourGoal = ourMoveCount = 0;
			}

			List<Move> actions = machine.getLegalMoves(state, role);
			Move randomMove = actions.get((new Random()).nextInt(actions.size()));

			if (actions.size() != 1) { // if there is only one possible move, don't let that i the overall outcome
				double curMobility, curFocus, curGoal;
				ourMobility += (curMobility = evalFuncMobilityOneStep(role, state));
				// ourFocus += evalFuncFocus(role, state);
				ourGoal += (curGoal = evalFuncGoal(role, state));
				ourMoveCount++;
			}

			List<Move> randomJointMove = machine.getRandomJointMove(state, role, randomMove);
			state = machine.getNextState(state, randomJointMove);
		}

		double sum = 0.0;
		for (int i = 0; i < NUM_WEIGHTS; i++) {
			values.set(i, values.get(i)/((gamesWeWon > 0) ? gamesWeWon : ourMoveCount));
			sum += values.get(i);
		}
		for (int i = 0; i < NUM_WEIGHTS; i++) weights[i] = values.get(i)/sum;

		System.out.println("Games Simulated: " + gamesSimulated);
		System.out.println("Our Values: " + values);
		System.out.println("# Games We Won: " + gamesWeWon);
		System.out.print("Our Weights: [");
		for (int i = 0; i < NUM_WEIGHTS; i++) System.out.print(weights[i] + ((i == NUM_WEIGHTS - 1) ? "]\n " : ", "));
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// TODO Auto-generated method stub

		StateMachine machine = getStateMachine();
		List<Role> roles = machine.getRoles();

		this.timeout = timeout - TIMEOUT_BUFFER;

		this.turn++;
		System.out.println("[" + getMatch().getGame().getName() + " | " + getMatch().getPlayerNamesFromHost() + "] (Turn " + this.turn + ") Score: " + machine.getGoal(getCurrentState(), getRole()) + " | State: " + getCurrentState());

		// since we finished implementing joint legal moves, we can *technically* use only one type of player
		if (roles.size() == 1) { // Use Complusive
			return selectMoveSinglePlayer();
		} else { // Use alpha-beta
			return selectMoveMultiPlayer();
		}
	}

	// MARK - Single Player (compulsive)
	private Move selectMoveSinglePlayer() throws MoveDefinitionException, GoalDefinitionException, TransitionDefinitionException {
		StateMachine machine = getStateMachine();
		Role role = getRole();
		MachineState state = getCurrentState();

		//We update to the current state of the game and get the next legal moves
		List<Move> actions = machine.getLegalMoves(state, role);

		// if there is only one move... then return immediately
		if (actions.size() == 1) return actions.get(0);

		//Get the first possible legal move
		Move bestAction = actions.get(0);
		int bestScore = 0;

		//keep iterating until time has reached the buffer point
		for (this.limit = 0; !reachingTimeout(); this.limit++) {
			//Go through each of the possible legal moves
			for (Move action : actions) {
				if (reachingTimeout()) break;

				//Get the result that gives the maximum score after going through the game tree
				int result = maxscore_complusive(role, machine.getNextState(state, Arrays.asList(action)), 0);

				//If our result is 100, then we cannot do any better
				if (result==100) return action;

				//Score should track the best result so far
				if (result > bestScore){
					bestScore = result;
					bestAction = action;
				}
			}
		}

		return bestAction;
	}

	private int maxscore_complusive(Role role, MachineState state, int level) throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException{
		StateMachine machine = getStateMachine();
		// Base Case
		if (machine.isTerminal(state)) return machine.getGoal(state, role);

		// if reached limit or timeout, do weighted eval func heuristic
		// This used to be the arbitrary Single player limit but now we do iterative deepening
		if (level >= this.limit || reachingTimeout()) {
			//This is the weighted heuristic function that we should decompose
			//return (int) ( (0.25 * evalFuncGoal(role, state)) + (0.5 * evalFuncMobilityNStep(role, state)) + (0.25 * evalFuncMobilityOneStep(role, state)) );

			//For now, only use Monte Carlo after iterative deepening
			return montecarlo(role, state, 30);
		}
		List<Move> actions = machine.getLegalMoves(state, role);
		int score = 0;
		for (int i = 0; i < actions.size(); i++) {
			if (reachingTimeout()) break;

			int result = maxscore_complusive(role, machine.getNextState(state, Arrays.asList(actions.get(i))), level+1);
			if(result>score) score = result;
		}
		return score;
	}

	// MARK - Multiplayer with fixed depth heuristic
	// NOTE: we were originally doing alpha-beta
	private Move selectMoveMultiPlayer() throws MoveDefinitionException, GoalDefinitionException, TransitionDefinitionException {
		StateMachine machine = getStateMachine();

		Role role = getRole();
		MachineState state = getCurrentState();

		//We update to the current state of the game and get the next legal moves
		List<Move> actions = machine.getLegalMoves(state, role);

		// if there is only one move... then return immediately
		if (actions.size() == 1) return actions.get(0);

		//Get the first possible legal move
		Move bestAction = actions.get(0);
		int bestScore = 0;

		/*Set alpha and beta
		int alpha = 0;
		int beta = 100;
		*/

		//iterative deepening: keep iterating till time has reached the buffer point
		for (this.limit = 0; !reachingTimeout(); this.limit++) {

			//Go through each of the possible legal moves
			for (Move action : actions) {
				if (reachingTimeout()) break;

				/*Get the result that gives the maximum score after going through the game tree
				 *Use alpha beta
				 *int result = minscore_ab(role, actions.get(i), state, alpha, beta);
				 */

				// Use bounded minimax with fixed Depth heuristic
				int result = minscore_minimax_fixedDepth(role, action, state, 0);

				//If our result is 100, then we cannot do any better
				if (result == 100) return action;

				//Score should track the best result so far
				if (result > bestScore){
					bestScore = result;
					bestAction = action;
				}
			}
		}

		return bestAction;
	}

	private int minscore_ab(Role role, Move action, MachineState state, int alpha, int beta) throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		StateMachine machine = getStateMachine();
		List<List<Move>> actions = machine.getLegalJointMoves(state, role, action);

		// Loop through all actions
		for (List<Move> a : actions) {
			if (reachingTimeout()) break;

			// get the new state we're going to be on
			MachineState newState = machine.getNextState(state, a);
			// System.out.println("Actions: " + actions);
			// and... recurse and do this all over again
			int result = maxscore_ab(role, newState, alpha, beta);
			beta = Math.min(beta, result);
			if (beta <= alpha) return alpha;
		}
		return beta;
	}

	private int maxscore_ab(Role role, MachineState state, int alpha, int beta) throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException{
		StateMachine machine = getStateMachine();
		// Base Case
		if (machine.isTerminal(state)) return machine.getGoal(state, role);

		List<Move> actions = machine.getLegalMoves(state, role);
		for (int i = 0; i < actions.size(); i++) {
			if (reachingTimeout()) break;

			int result = minscore_ab(role, actions.get(i), state, alpha, beta);
			alpha = Math.max(alpha, result);
			if (alpha >= beta) return beta;
		}
		return alpha;
	}

	private int minscore_minimax_fixedDepth(Role role, Move action, MachineState state, int level) throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		StateMachine machine = getStateMachine();
		List<List<Move>> actions = machine.getLegalJointMoves(state, role, action);

		int score = 100;

		// Loop through all actions
		for (List<Move> a : actions) {
			if (reachingTimeout()) break;

			// get the new state we're going to be on
			MachineState newState = machine.getNextState(state, a);
			// System.out.println("Actions: " + actions);
			// and... recurse and do this all over again
			int result = maxscore_minimax_fixedDepth(role, newState, level + 1);

			// make sure we only get the minimum score
			if (result == 0) return 0;
			if (result < score) score = result;
		}
		return score;
	}

	private int maxscore_minimax_fixedDepth(Role role, MachineState state, int level) throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException{
		StateMachine machine = getStateMachine();
		List<Role> roles = machine.getRoles();

		// get the opponent
		Role opponent = (role.equals(roles.get(0))) ? roles.get(1) : roles.get(0);

		// Base Case
		// If we reach a terminal state then just return the reward/goal of the state
		if (machine.isTerminal(state)) {
			// System.out.println(machine.getGoal(state, role));
			return machine.getGoal(state, role);
		}
		//ASSIGN 3 NUMBER 4: OPPONENT FOCUS HEURISTIC
		//Could also do opponent mobility
		//Assuming that opponent eval func replaces our own eval func, so have to delete number 3
		/*if (level >= limitMultiPlayer) {
			return evalFuncFocus(opponent, state);
		}*/

		//System.out.println("On Level " + level + " with limit " + this.limit + ".");

		//If we reach a non-terminal state but have the limit level or timeout, do an evaluation function heuristic
		// This used to be the arbitrary Multi player limit but now we do iterative deepening
		if (level >= this.limit || reachingTimeout()) {
			//return evalFunc(role, state); // decided to decomp this long line

			//For now, just return Monte Carlo Search
			return montecarlo(role, state, 30);
		}
		List<Move> actions = machine.getLegalMoves(state, role);
		int score = 0;
		for (int i = 0; i < actions.size(); i++) {
			if (reachingTimeout()) break;

			int result = minscore_minimax_fixedDepth(role, actions.get(i), state, level);
			if(result == 100) return 100;
			if(result > score) score = result;
		}
		return score;
	}

	private int evalFunc(Role role, MachineState state) throws MoveDefinitionException, GoalDefinitionException {
		// combined evalulation function
		return (int) (weights[0] * evalFuncMobilityOneStep(role, state) + weights[1] * evalFuncFocus(role, state) + weights[2] * evalFuncGoal(role, state));

		// kept this for backup reasons
		// return (int) ( (0.45 * evalFuncGoal(role, state)) + (0.45 * evalFuncMobilityOneStep(role, state)) + (0.10 * evalFuncFocus(opponent, state)) );
	}

	private int evalFuncGoal(Role role, MachineState state) throws MoveDefinitionException, GoalDefinitionException {
		StateMachine machine = getStateMachine();
		return machine.getGoal(state, role);
	}

	private int evalFuncMobilityOneStep(Role role, MachineState state) throws MoveDefinitionException {
		StateMachine machine = getStateMachine();

		//We update to the current state of the game and get the next legal moves
		List<Move> actions = machine.getLegalMoves(state, role);
		List<Move> feasibles = machine.findActions(role);

		return (int)((double)actions.size()/feasibles.size() * 100);
	}

	private int evalFuncMobilityNStepHelper(Role role, MachineState state, int xthStep) throws MoveDefinitionException, TransitionDefinitionException{
		StateMachine machine = getStateMachine();
		List<Role> roles = machine.getRoles();
		int sumMobility = 0;

		List<Move> actions = machine.getLegalMoves(state, role);
		if (machine.isTerminal(state)) {
			return 0; // No valid legal moves
		}
		if (xthStep >= NTH_STEP_MOBILITY_LIMIT) {
			return actions.size();
		}
		for (Move a: actions) {
			List<Move> toMove = null;
			// Make sure we perform the moves in the right order

			/*
			// ASSUME THERE IS ONLY ONE PLAYER!!!!!!!!!!!!!!!
			if (role.equals(roles.get(0))) {
				toMove = Arrays.asList(action, a);
			} else {
				toMove = Arrays.asList(a, action);
			}
			*/

			// get the new state we're going to be on
			MachineState newState = machine.getNextState(state, Arrays.asList(a));
			sumMobility += evalFuncMobilityNStepHelper(role, state, xthStep + 1);
		}

		return sumMobility;
	}

	private int evalFuncMobilityNStep(Role role, MachineState state) throws MoveDefinitionException, TransitionDefinitionException {
		StateMachine machine = getStateMachine();
		// Call helper method to find number of legal moves in nth step
		int legalActions = evalFuncMobilityNStepHelper(role, state, 0);

		// Once we reach the nth step level then find the mobility (number of steps that can be made in that state)

		List<Move> feasibles = machine.findActions(role);

		return (int)((double)legalActions/feasibles.size() * 100);
	}

	private int evalFuncFocus(Role role, MachineState state) throws MoveDefinitionException {
		StateMachine machine = getStateMachine();

		//We update to the current state of the game and get the next legal moves
		List<Move> actions = machine.getLegalMoves(state, role);
		List<Move> feasibles = machine.findActions(role);

		return (int)(100-(double)actions.size()/feasibles.size() * 100);
	}

	private int evalFuncBasic(Role role, MachineState state) {
		return 0;
	}

	private int montecarlo(Role role, MachineState state, int count) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		int total = 0;
		for (int i = 0; i < count; i++) total += depthCharge(role, state);
		return total/count;
	}

	private int depthCharge(Role role, MachineState state) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		StateMachine machine = getStateMachine();
		while (!machine.isTerminal(state)) {
			state = machine.getNextState(state, machine.getRandomJointMove(state));
		}
		return machine.getGoal(state, role);
	}

	private boolean reachingTimeout() {
		return System.currentTimeMillis() > this.timeout;
	}

	@Override
	public void stateMachineStop() {
		// TODO Auto-generated method stub

	}

	@Override
	public void stateMachineAbort() {
		// TODO Auto-generated method stub

	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
		// TODO Auto-generated method stub

	}

	@Override
	public String getName() {
		// TODO Auto-generated method stub
		return "418 I'm a Teapot";
	}

}
