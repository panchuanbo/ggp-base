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

		//We update to the current state of the game and get the next legal moves
		List<Move> actions = machine.getLegalMoves(state, role);

		//Get the first possible legal move
		Move action = actions.get(0);
		int score = 0;

		//Go through each of the possible legal moves
		for (int i=0; i<actions.size(); i++){

			//Get the result that gives the maximum score after going through the game tree
			int result = maxscore(role, machine.getNextState(state, Arrays.asList(actions.get(i))));

			//If our result is 100, then we cannot do any better
			if (result==100){
				return actions.get(i);
			}

			//Score should track the best result so far
			if (result>score){
				score = result;
				action = actions.get(i);

			}
		}

		return action;
	}



	private int maxscore(Role role, MachineState state) throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException{
		StateMachine machine = getStateMachine();
		// Base Case
		if (machine.isTerminal(state)) {
			return machine.getGoal(state, role);
		}
		List<Move> actions = machine.getLegalMoves(state, role);
		int score = 0;
		for (int i = 0; i < actions.size(); i++) {
			int result = maxscore(role, machine.getNextState(state, Arrays.asList(actions.get(i))));
			if(result>score) score = result;
		}
		return score;
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
