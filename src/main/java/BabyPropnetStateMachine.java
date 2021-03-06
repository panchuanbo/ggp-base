import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.math3.analysis.function.Constant;
import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.And;
import org.ggp.base.util.propnet.architecture.components.Not;
import org.ggp.base.util.propnet.architecture.components.Or;
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

public class BabyPropnetStateMachine extends StateMachine {

	private PropNet propnet;
	private List<Role> roles;

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
			System.out.println("Terminal Proposition: " + this.propnet.getTerminalProposition());
			//System.out.println("Wrote propnet to disk.");
			//this.propnet.renderToFile("C:\\Users\\panch\\Desktop\\propnet.out");
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	@Override
	public int getGoal(MachineState state, Role role) throws GoalDefinitionException {
		this.clearpropnet();
		this.markbases(state);
		Set<Proposition> goalProps = this.propnet.getGoalPropositions().get(role);
		for (Proposition p : goalProps) {
			if (prop(p)) return this.getGoalValue(p);
		}
		return 0;
	}

	@Override
	public boolean isTerminal(MachineState state) {
		this.clearpropnet();
		this.markbases(state);
		for (Component c : this.propnet.getTerminalProposition().getInputs()) {
			if (!prop(c)) return false;
		}

		return true;
	}

	@Override
	public List<Role> getRoles() {
		return roles;
	}

	@Override
	public MachineState getInitialState() {
		this.clearpropnet();
		this.propnet.getInitProposition().setValue(true);
		Set<GdlSentence> state = new HashSet<GdlSentence>();
//		System.out.println("Start Initial State Prop");
		for (Proposition base : this.propnet.getBasePropositions().values()) {
			if (prop(base.getSingleInput())) state.add(base.getName());
		}
//		System.out.println("End Initial State Prop");
		System.out.println("INITIAL STATE VALUES: " + state);
		return new MachineState(state);
	}

	@Override
	public List<Move> getLegalMoves(MachineState state, Role role) throws MoveDefinitionException {
		this.clearpropnet();
		this.markbases(state);
		Set<Proposition> legalProps = this.propnet.getLegalPropositions().get(role);
		ArrayList<Move> moves = new ArrayList<Move>();
//		System.out.println("Start Legal Moves Prop");
		for (Proposition p : legalProps) {
			if (prop(p.getSingleInput())) moves.add(this.getMoveFromProposition(p));
		}
//		System.out.println("End Legal Moves Prop");
		System.out.println("Legal Moves: " + moves);
		return moves;
	}

	@Override
	public MachineState getNextState(MachineState state, List<Move> moves) throws TransitionDefinitionException {
//		System.out.println("[getNextState] @param state: " + state);
//		System.out.println("[getNextState] @param moves: " + moves);
		this.clearpropnet();
		this.markactions(moves);
		this.markbases(state);
		Set<GdlSentence> gdlState = new HashSet<GdlSentence>();
//		System.out.println("Start Get Next State Prop");
//		System.out.println("Base Prop: " + this.propnet.getBasePropositions().values());
		for (Proposition base : this.propnet.getBasePropositions().values()) {
//			System.out.println("Proposition: " + base + " | value: " + base.getValue());
//			if (prop(base.getSingleInput())) {System.out.println("Input True?"); gdlState.add(base.getName());}
			if (prop(base.getSingleInput())) gdlState.add(base.getName());
		}
//		System.out.println("End Get Next State Prop");
		System.out.println("NEXT STATE VALUES: " + gdlState);
		return new MachineState(gdlState);
	}

	// ----------------------------------------------

	private boolean prop(Component p) {
//		System.out.println("Class: " + p.getClass());
//		if (this.propnet.getBasePropositions().containsValue(p)) {System.out.println("reached base " + ((Proposition)p).getName() + " with val: " + p.getValue()); return p.getValue();}
		if (this.propnet.getBasePropositions().containsValue(p)) return p.getValue();
		if (this.propnet.getInputPropositions().containsValue(p)) return p.getValue();
		if (p.getClass().equals(And.class)) return propAND(p);
		if (p.getClass().equals(Transition.class)) return propOR(p);
		if (p.getClass().equals(Or.class)) return propOR(p);
		if (p.getClass().equals(Not.class)) return propNOT(p);
		if (p.getClass().equals(Constant.class)) return p.getValue();
		if (p.getInputs().size() == 0) return p.getValue();

		return prop(p.getSingleInput());
	}

	private boolean propAND(Component p) {
		for (Component c : p.getInputs()) if (!prop(c)) return false;
		return true;
	}

	private boolean propOR(Component p) {
		for (Component c : p.getInputs()) if (prop(c)) return true;
		return false;
	}

	private boolean propNOT(Component p) {
		return !prop(p.getSingleInput());
	}

	private void markbases(MachineState s) {
		for (GdlSentence sentence : s.getContents()) {
			this.propnet.getBasePropositions().get(sentence).setValue(true);
		}
	}

	private void markactions(List<Move> moves) {
		List<GdlSentence> gdlMoves = toDoes(moves);
		for (GdlSentence m : gdlMoves) {
			this.propnet.getInputPropositions().get(m).setValue(true);
		}
	}

	private void clearpropnet() {
		for (Proposition p : this.propnet.getPropositions()) p.setValue(false);
	}

    /**
     * The Input propositions are indexed by (does ?player ?action).
     *
     * This translates a list of Moves (backed by a sentence that is simply ?action)
     * into GdlSentences that can be used to get Propositions from inputPropositions.
     * and accordingly set their values etc.  This is a naive implementation when coupled with
     * setting input values, feel free to change this for a more efficient implementation.
     *
     * @param moves
     * @return
     */
    private List<GdlSentence> toDoes(List<Move> moves) {
    	List<GdlSentence> doeses = new ArrayList<GdlSentence>(moves.size());
        Map<Role, Integer> roleIndices = getRoleIndices();

        for (int i = 0; i < roles.size(); i++)
        {
            int index = roleIndices.get(roles.get(i));
            doeses.add(ProverQueryBuilder.toDoes(roles.get(i), moves.get(index)));
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
