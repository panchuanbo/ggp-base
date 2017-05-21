import java.util.ArrayList;
import java.util.BitSet;
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

public class AnEvenBetterPropnetStateMachine extends StateMachine {

	private int[] components;
	private long[] componentInfo;
	private int[] connectivity;
	private PropNet propnet;

	private List<Role> roles;
	private Proposition[] basePropositions;
	private Proposition[] inputPropositions;
	private ArrayList<Map<GdlTerm, GdlSentence>> inputMap;
	private Map<Role, Proposition[]> legalPropositions;

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

			int numOutputs = 0, id = 0;
			Set<Component> comps = this.propnet.getComponents();
			for (Component c : comps) {
				numOutputs += c.numberOfOutputs();
				c.componentId = id;
				id++;
			}


			components = new int[comps.size()];
			componentInfo = new long[comps.size()];
			connectivity = new int[numOutputs];

			int outputloc = 0;
			for (Component c : comps) {

			}

			this.basePropositions = new Proposition[this.propnet.getBasePropositions().size()];
			this.inputPropositions = new Proposition[this.propnet.getInputPropositions().size()];
			this.legalPropositions = new HashMap<>();

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

			Map<Role, Set<Proposition>> legalprops = this.propnet.getLegalPropositions();
			for (Role r : this.roles) {
				Set<Proposition> legals = legalprops.get(r);
				Proposition[] ps = new Proposition[legals.size()];
				int i = 0;
				for (Proposition p : legals) {
					ps[i] = p;
					i++;
				}
				this.legalPropositions.put(r, ps);
			}

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
		for (Component c : this.propnet.getComponents()) { // check what subclass of component
			if ((c instanceof And)) ((And) c).useFastMethod = true;
			if ((c instanceof Or)) ((Or) c).useFastMethod = true;
			if ((c instanceof Transition)) ((Transition) c).useFastMode = true;
			c.setPreviousValue(false);
		}
		for (Component c : this.propnet.getComponents()) if ((c instanceof Not)) forwardprop(c);
		forwardprop(this.propnet.getInitProposition());

		Set<GdlSentence> state = new HashSet<GdlSentence>();
		BitSet activeStates = new BitSet(this.basePropositions.length);
		for (int i = 0; i < this.basePropositions.length; i++) {
			boolean val = this.basePropositions[i].fasterGetSingleInput().getValue();
			activeStates.set(i, val);
			if (val) {
				state.add(this.basePropositions[i].getName());
			}
		}
		System.out.println("INITIAL STATE VALUES: " + state);
		this.propnet.getInitProposition().setValue(false);
		forwardprop(this.propnet.getInitProposition());
		return new MachineState(state, activeStates);
	}

	@Override
	public List<Move> getLegalMoves(MachineState state, Role role) throws MoveDefinitionException {
		this.markbases(state);
		for (Component c : this.basePropositions) forwardprop(c);
//		for (Component c : this.propnet.getComponents()) c.setPreviousValue(c.getValue());
		Proposition[] legalProps = this.legalPropositions.get(role);
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
		BitSet activeStates = new BitSet(this.basePropositions.length);
		for (int i = 0; i < this.basePropositions.length; i++) {
			boolean val = this.basePropositions[i].fasterGetSingleInput().getValue();
			activeStates.set(i, val);
			if (val) {
				gdlState.add(this.basePropositions[i].getName());
			}
		}
//		System.out.println("NEXT STATE VALUES: " + gdlState);

		return new MachineState(gdlState, activeStates);
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
			else if ((o instanceof And)) ((And) o).counter += (c_val) ? 1 : -1;
			else if ((o instanceof Or)) ((Or) o).counter += (c_val) ? 1 : -1;
			else if ((o instanceof Transition)) {
				o.setPreviousValue(o.getValue());
				((Transition) o).setValue(c_val);
			}
			forwardprop(o);
		}
	}

	private void markbases(MachineState s) {
		BitSet activeBits = s.getPropContents();
		for (int i = 0; i < this.basePropositions.length; i++) {
			this.basePropositions[i].setPreviousValue(this.basePropositions[i].getValue());
			this.basePropositions[i].setValue(activeBits.get(i));
		}
//		for (Proposition p : this.basePropositions) {
//			p.setPreviousValue(p.getValue());
//			p.setValue(false);
//		}
//		for (GdlSentence sentence : s.getContents()) {
//			this.propnet.getBasePropositions().get(sentence).setValue(true);
//		}
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
