import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.propnet.factory.OptimizingPropNetFactory;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class BabyPropnetStateMachine extends StateMachine {

	private PropNet propnet;

	@Override
	public List<Move> findActions(Role role) throws MoveDefinitionException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void initialize(List<Gdl> description) {
		try {
			this.propnet = OptimizingPropNetFactory.create(description);
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	@Override
	public int getGoal(MachineState state, Role role) throws GoalDefinitionException {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean isTerminal(MachineState state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public List<Role> getRoles() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public MachineState getInitialState() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<Move> getLegalMoves(MachineState state, Role role) throws MoveDefinitionException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public MachineState getNextState(MachineState state, List<Move> moves) throws TransitionDefinitionException {
		// TODO Auto-generated method stub
		return null;
	}

	// ----------------------------------------------

	private void markbases(boolean[] vals) {
		int loc = 0;
	    Iterator it = this.propnet.getBasePropositions().entrySet().iterator();
	    while (it.hasNext()) {
	        Map.Entry pair = (Map.Entry)it.next();
	        ((Proposition)pair.getValue()).setValue(vals[loc]);
	        loc++;
	    }
	}

	private void markactions() {
	}

	private void clearpropnet() {
	    Iterator it = this.propnet.getBasePropositions().entrySet().iterator();
	    while (it.hasNext()) {
	        Map.Entry pair = (Map.Entry)it.next();
	        ((Proposition)pair.getValue()).setValue(false);
	    }
	}

	/*
	 *

function markactions (vector,propnet)
 {var props = propnet.actions;
  for (var i=0; i<props.length; i++)
      {props[i].mark = vector[i]};
  return true}
	 */

	// ----------------------------------------------

}
