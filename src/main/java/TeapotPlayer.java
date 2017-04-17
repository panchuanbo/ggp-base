import java.util.Arrays;
import java.util.List;

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

	Player p;
	// This is Nidhi

	@Override
	public StateMachine getInitialStateMachine() {
		// TODO Auto-generated method stub
		return new CachedStateMachine(new ProverStateMachine());
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// TODO Auto-generated method stub

	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// TODO Auto-generated method stub

		StateMachine machine = getStateMachine();
		Role role = getRole();
		MachineState state = getCurrentState();
		// System.out.println(state.getContents());
		// System.out.println(machine.getLegalJointMoves(state));

		//We update to the current state of the game and get the next legal moves
		List<Move> actions = machine.getLegalMoves(state, role);

		//Get the first possible legal move
		Move action = actions.get(0);
		int score = 0;

		//Go through each of the possible legal moves
		for (int i=0; i < actions.size(); i++){

			//Get the result that gives the maximum score after going through the game tree
			int result = minscore_minimax(role, actions.get(i), state);

			//If our result is 100, then we cannot do any better
			/*if (result==100){
				return actions.get(i);
			}*/

			// System.out.println(actions.get(i) + " " + result);

			//Score should track the best result so far
			if (result > score){
				score = result;
				action = actions.get(i);
			}
		}
		// System.out.println();

		return action;
	}

	private int minscore_minimax(Role role, Move action, MachineState state) throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		StateMachine machine = getStateMachine();
		List<Role> roles = machine.getRoles();

		// get the opponent
		Role opponent = (role.equals(roles.get(0))) ? roles.get(1) : roles.get(0);
		// System.out.println(role.equals(opponent));
		List<Move> actions = machine.getLegalMoves(state, opponent);

		int score = 100;

//		if (machine.isTerminal(state)) {
//			return machine.getGoal(state, role);
//		}

		// Loop through all actions
		for (Move a : actions) {
			List<Move> toMove = null;

			// Make sure we perform the moves in the right order
			if (role.equals(roles.get(0))) {
				toMove = Arrays.asList(action, a);
			} else {
				toMove = Arrays.asList(a, action);
			}

			// get the new state we're going to be on
			MachineState newState = machine.getNextState(state, toMove);
			// System.out.println("Actions: " + actions);

			// and... recurse and do this all over again
			int result = maxscore_minimax(role, newState);

			// make sure we only get the minimum score
			//if (result == 0) return 0;
			if (result < score) score = result;
		}

		return score;
	}

	private int maxscore_minimax(Role role, MachineState state) throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException{
		StateMachine machine = getStateMachine();
		// Base Case
		if (machine.isTerminal(state)) {
			// System.out.println(machine.getGoal(state, role));
			return machine.getGoal(state, role);
		}
		List<Move> actions = machine.getLegalMoves(state, role);
		int score = 0;
		for (int i = 0; i < actions.size(); i++) {
			int result = minscore_minimax(role, actions.get(i), state);
			//if(result == 100) return 100;
			if(result > score) score = result;
		}
		return score;
	}

/* maxscore for complusive :D
	private int maxscore_complusive(Role role, MachineState state) throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException{
		StateMachine machine = getStateMachine();
		// Base Case
		if (machine.isTerminal(state)) {
			return machine.getGoal(state, role);
		}
		List<Move> actions = machine.getLegalMoves(state, role);
		int score = 0;
		for (int i = 0; i < actions.size(); i++) {
			int result = maxscore_complusive(role, machine.getNextState(state, Arrays.asList(actions.get(i))));
			if(result>score) score = result;
		}
		return score;
	}
*/

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
