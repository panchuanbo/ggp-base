import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.gdl.grammar.GdlTerm;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.Not;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.propnet.architecture.components.Transition;
import org.ggp.base.util.propnet.factory.OptimizingPropNetFactory;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;

public class HopefullyBetterPropnetStateMachineQuestionMark extends StateMachine {

	private PropNet propnet;
	private List<Role> roles;
	private Proposition[] basePropositions;
	private Proposition[] inputPropositions;
	private ArrayList<Map<GdlTerm, GdlSentence>> inputMap;

//	private int[] inputsPerRole;
//	private int[] mapToBetterInputMap;
//	private GdlSentence[] betterInputMap;

	@Override
	public List<Move> findActions(Role role) throws MoveDefinitionException {
		Set<Proposition> legalProps = this.propnet.getLegalPropositions().get(role);
		ArrayList<Move> legalMoves = new ArrayList<Move>();
		for (Proposition p : legalProps) {
			legalMoves.add(this.getMoveFromProposition(p));
		}
		return legalMoves;
	}

	@Override
	public void initialize(List<Gdl> description) {
		try {
			this.propnet = OptimizingPropNetFactory.create(description);
			this.roles = propnet.getRoles();
			for (Component c : this.propnet.getComponents()) c.crystalize();
			this.basePropositions = new Proposition[this.propnet.getBasePropositions().size()];
			this.inputPropositions = new Proposition[this.propnet.getInputPropositions().size()];

			List<Proposition> bases = new ArrayList<Proposition>(this.propnet.getBasePropositions().values());
			for (int i = 0; i < this.basePropositions.length; i++) {
				this.basePropositions[i] = bases.get(i);
				this.basePropositions[i].setBase(true);
			}

			List<Proposition> inputs = new ArrayList<Proposition>(this.propnet.getInputPropositions().values());
			for (int i = 0; i < this.inputPropositions.length; i++) {
				this.inputPropositions[i] = inputs.get(i);
				this.inputPropositions[i].setInput(true);
			}

//			this.inputsPerRole = new int[this.roles.size()];
//			int total = 0;
//			for (int i = 0; i < this.roles.size(); i++) {
//				int sz = this.propnet.getLegalPropositions().get(roles.get(i)).size();
//				this.inputsPerRole[i] = sz;
//				total += sz;
//			}
//			this.mapToBetterInputMap = new int[total];
//			this.betterInputMap = new GdlSentence[total];
//
//			for (int i = 0; i < this.roles.size(); i++) {
//				Role r = this.roles.get(i);
//				Set<Proposition> moves = this.propnet.getLegalPropositions().get(r);
//				Map<GdlTerm, GdlSentence> buf = new HashMap<>();
//				for (Proposition p : moves) {
//					GdlSentence moveSentence = ProverQueryBuilder.toDoes(r, new Move(p.getName().get(1)));
//					buf.put(p.getName().get(1), moveSentence);
////					System.out.println("key: " + p.getName().get(1) + " | value: " + moveSentence);
//				}
//			}
//
			this.inputMap = new ArrayList<>();

			for (Role r : this.roles) {
				Set<Proposition> moves = this.propnet.getLegalPropositions().get(r);
				Map<GdlTerm, GdlSentence> buf = new HashMap<>();
				for (Proposition p : moves) {
					GdlSentence moveSentence = ProverQueryBuilder.toDoes(r, new Move(p.getName().get(1)));
					buf.put(p.getName().get(1), moveSentence);
//					System.out.println("key: " + p.getName().get(1) + " | value: " + moveSentence);
				}
				this.inputMap.add(buf);
			}
			// System.out.println("input map: " + this.inputMap);
			//System.out.println("Wrote propnet to disk.");
//			this.propnet.renderToFile("C:\\Users\\panch\\Desktop\\connect4.dot");
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	@Override
	public int getGoal(MachineState state, Role role) throws GoalDefinitionException {
		this.markbases(state);
		for (Component c : this.basePropositions) forwardprop(c);
		Set<Proposition> goalProps = this.propnet.getGoalPropositions().get(role);
		for (Proposition p : goalProps) {
			if (p.getValue()) return this.getGoalValue(p);
		}
		return 0;
	}

	@Override
	public boolean isTerminal(MachineState state) {
		this.markbases(state);
		for (Component c : this.basePropositions) forwardprop(c);
		for (Component c : this.propnet.getTerminalProposition().fasterGetInputs()) {
			if (!c.getValue()) return false;
		}

		return true;
	}

	@Override
	public List<Role> getRoles() {
		return this.roles;
	}

	@Override
	public MachineState getInitialState() {
		this.propnet.getInitProposition().setValue(true);
		for (Component c : this.propnet.getComponents()) c.setPreviousValue(false);
		for (Component c : this.propnet.getComponents()) if ((c instanceof Not)) forwardprop(c);
		forwardprop(this.propnet.getInitProposition());

		Set<GdlSentence> state = new HashSet<GdlSentence>();
		for (Proposition base : this.basePropositions) {
			if (base.fasterGetSingleInput().getValue()) state.add(base.getName());
		}
//		for (Component c : this.propnet.getComponents()) c.setPreviousValue(c.getValue());
		System.out.println("INITIAL STATE VALUES: " + state);
		this.propnet.getInitProposition().setValue(false);
		return new MachineState(state);
	}

	@Override
	public List<Move> getLegalMoves(MachineState state, Role role) throws MoveDefinitionException {
		this.markbases(state);
		for (Component c : this.basePropositions) forwardprop(c);
//		for (Component c : this.propnet.getComponents()) c.setPreviousValue(c.getValue());
		Set<Proposition> legalProps = this.propnet.getLegalPropositions().get(role);
		ArrayList<Move> moves = new ArrayList<Move>();
		for (Proposition p : legalProps) {
			if (p.getValue()) moves.add(this.getMoveFromProposition(p));
		}
//		System.out.println("Legal Moves: " + moves);
		return moves;
	}

	@Override
	public MachineState getNextState(MachineState state, List<Move> moves) throws TransitionDefinitionException {
		this.markactions(moves);
		this.markbases(state);
		for (Component c : this.basePropositions) forwardprop(c);
		for (Component c : this.inputPropositions) forwardprop(c);
//		for (Component c : this.propnet.getComponents()) c.setPreviousValue(c.getValue());
		Set<GdlSentence> gdlState = new HashSet<GdlSentence>();
		for (Proposition base : this.basePropositions) {
			if (base.fasterGetSingleInput().getValue()) gdlState.add(base.getName());
		}
//		System.out.println("NEXT STATE VALUES: " + gdlState);

		return new MachineState(gdlState);
	}

	// ----------------------------------------------

	private void forwardprop(Component c) {
		boolean c_val = c.getValue();
		if (c_val == c.previousValue()) return;
		c.setPreviousValue(c_val);
		if ((c instanceof Transition)) return;
		for (Component o : c.fasterGetOutputs()) {
			if ((o instanceof Proposition)) {
				o.setPreviousValue(o.getValue());
				((Proposition) o).setValue(c_val);
			}
			forwardprop(o);
		}
	}

	private void markbases(MachineState s) {
		for (Proposition p : this.basePropositions) {
			p.setPreviousValue(p.getValue());
			p.setValue(false);
		}
		for (GdlSentence sentence : s.getContents()) {
			this.propnet.getBasePropositions().get(sentence).setValue(true);
		}
	}

	private void markactions(List<Move> moves) {
		for (Proposition p : this.inputPropositions) {
			p.setPreviousValue(p.getValue());
			p.setValue(false);
		}
		GdlSentence[] gdlMoves = toDoes(moves);
		for (GdlSentence m : gdlMoves) {
			this.propnet.getInputPropositions().get(m).setValue(true);
		}
	}

    private GdlSentence[] toDoes(List<Move> moves) {
    	GdlSentence[] doeses = new GdlSentence[moves.size()];
    	for (int i = 0; i < moves.size(); i++) {
    		doeses[i] = this.inputMap.get(i).get(moves.get(i).getContents());
    	}
    	return doeses;
    }

    /**
     * Takes in a Legal Proposition and returns the appropriate corresponding Move
     * @param p
     * @return a PropNetMove
     */
    public Move getMoveFromProposition(Proposition p) {
        return new Move(p.getName().get(1));
    }

    /**
     * Helper method for parsing the value of a goal proposition
     * @param goalProposition
     * @return the integer value of the goal proposition
     */
    private int getGoalValue(Proposition goalProposition) {
        GdlRelation relation = (GdlRelation) goalProposition.getName();
        GdlConstant constant = (GdlConstant) relation.get(1);
        return Integer.parseInt(constant.toString());
    }
	// ----------------------------------------------

}
