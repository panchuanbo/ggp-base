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
import org.ggp.base.util.propnet.architecture.components.Constant;
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

	private int[] componentValues;
	private int[] componentMetadata;
	private int[] componentConnectivity;
	private int inputOffset;
	private int everythingElseOffset;

	private int terminalID;
	private int initID;
	private int numberOfBaseProps;
	private int numberOfInputProps;
	private int numberOfPropositions;
	private int notStart, notEnd;
	private int[] baseToTransition;

	private PropNet propnet;

	private List<Role> roles;
	private GdlSentence[] baseToSentence;
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
			for (Component c : this.propnet.getComponents()) c.crystalize();

			int numOutputs = 0, id = 0;
			for (Component c : this.propnet.getBasePropositions().values()) {
				numOutputs += c.numberOfOutputs();
				c.componentId = id;
//				System.out.println("Base: " + c.toString() + " | id: " + id);
				id++;
			}
			this.inputOffset = id;
			for (Component c : this.propnet.getInputPropositions().values()) {
				numOutputs += c.numberOfOutputs();
				c.componentId = id;
//				System.out.println("Input: " + c.toString() + " | id: " + id);
				id++;
			}
			this.everythingElseOffset = id;
			for (Proposition p : this.propnet.getPropositions()) {
				if (p.componentId == Integer.MIN_VALUE) {
					numOutputs += p.numberOfOutputs();
					p.componentId = id;
					id++;
				}
			}
			Set<Component> comps = this.propnet.getComponents();
			this.notStart = id;
			for (Component c : comps) {
				if ((c instanceof Not)) {
					if (c.componentId == Integer.MIN_VALUE) {
						numOutputs += c.numberOfOutputs();
						c.componentId = id;
						id++;
					}
				}
			}
			this.notEnd = id;
			for (Component c : comps) {
				if (c.componentId == Integer.MIN_VALUE) {
					numOutputs += c.numberOfOutputs();
					c.componentId = id;
					id++;
				}
			}

			this.numberOfBaseProps = this.propnet.getBasePropositions().size();
			this.numberOfInputProps = this.propnet.getInputPropositions().size();
			this.numberOfPropositions = this.propnet.getPropositions().size();
			System.out.println("Number of Base Props: " + this.propnet.getBasePropositions().size());
			System.out.println("Number of Input Props: " + this.propnet.getInputPropositions().size());

			this.terminalID = this.propnet.getTerminalProposition().componentId;
			if (this.propnet.getInitProposition() != null) {
				this.initID = this.propnet.getInitProposition().componentId;
			} else {
				this.initID = -1;
			}

			System.out.println("Number of Propositions: " + this.numberOfPropositions);
			System.out.println("Terminal Proposition Component ID: " + this.terminalID);
			System.out.println("Input Proposition Component ID: " + this.initID);

			componentValues = new int[comps.size()]; 			// holds the number
			componentMetadata = new int[comps.size()];			// holds #outputs + output offset
			componentConnectivity = new int[numOutputs];		// holds list of outputs
			int outputloc = 0;
			for (Component c : comps) {
				if ((c instanceof Or)) componentValues[c.componentId] = 0x7FFFFFFF;
				else if ((c instanceof And)) componentValues[c.componentId] = 0x80000000 - c.numberOfInputs();
				else if ((c instanceof Not)) componentValues[c.componentId] = 0;
				else if ((c instanceof Constant)) {
					System.out.println("we have constants :O");

					componentValues[c.componentId] = (c.getValue()) ? 0 : -1;//0xFFFFFFFF : 0;
				}
				else componentValues[c.componentId] = 0x7FFFFFFF;
				componentMetadata[c.componentId] = (c.numberOfOutputs() << 16) + (outputloc);



				int num_loc = this.componentMetadata[c.componentId];
				int result_num = (num_loc & 0xFFFF0000) >>> 16;
				int result_loc = (num_loc & 0xFFFF);
				assert(result_num == c.numberOfOutputs());
				assert(result_loc == outputloc);

				for (Component o : c.getOutputs()) {
					if ((o instanceof Transition)) componentConnectivity[outputloc] = -o.componentId;
					else componentConnectivity[outputloc] = o.componentId;
					outputloc++;
				}
			}

			System.out.println("Num Outputs: " + numOutputs);
			System.out.println("Output Loc: " + outputloc);

			this.baseToTransition = new int[this.numberOfBaseProps];
			this.baseToSentence = new GdlSentence[this.numberOfBaseProps];
			this.inputPropositions = new Proposition[this.numberOfInputProps];
			this.legalPropositions = new HashMap<>();

			List<Proposition> bases = new ArrayList<Proposition>(this.propnet.getBasePropositions().values());
			for (int i = 0; i < this.numberOfBaseProps; i++) {
				this.baseToTransition[bases.get(i).componentId] = bases.get(i).fasterGetSingleInput().componentId;
				this.baseToSentence[bases.get(i).componentId] = bases.get(i).getName();
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
		System.out.println("Finished Initializing StateMachine");
	}

	@Override
	public int getGoal(MachineState state, Role role) throws GoalDefinitionException {
		BitSet b = state.getPropContents();
		for (int i = 0; i < this.numberOfBaseProps; i++) forwardprop_wrapper(i, b.get(i));
		Set<Proposition> goalProps = this.propnet.getGoalPropositions().get(role);
		for (Proposition p : goalProps) {
			if (this.componentValues[p.componentId] < 0) {
//				System.out.println("ayy... I found a goal :)");
				return this.getGoalValue(p);
			}
		}
		return 0;
	}

	@Override
	public boolean isTerminal(MachineState state) {
		BitSet b = state.getPropContents();
		for (int i = 0; i < this.numberOfBaseProps; i++) {
			forwardprop_wrapper(i, b.get(i));
		}
		return (this.componentValues[this.terminalID] < 0);
	}

	@Override
	public List<Role> getRoles() {
		return this.roles;
	}

	@Override
	public MachineState getInitialState() {
		for (Component c : this.propnet.getComponents()) { // check what subclass of component
			if ((c instanceof And)) ((And) c).useFastMethod = true;
			if ((c instanceof Or)) ((Or) c).useFastMethod = true;
			if ((c instanceof Transition)) ((Transition) c).useFastMode = true;
		}
		if (this.initID != -1) this.propnet.getInitProposition().setValue(true);
		for (Component c : this.propnet.getComponents()) {
			if ((c instanceof Constant)) forwardprop_wrapper(c.componentId, c.getValue());
			else if ((c instanceof Not)) forwardprop_wrapper(c.componentId, c.getValue());
		}
		if (this.initID != -1) forwardprop_wrapper(this.initID, true);

		Set<GdlSentence> state = new HashSet<GdlSentence>();
		BitSet activeStates = new BitSet(this.numberOfBaseProps);
		for (int id = 0; id < this.numberOfBaseProps; id++) {
			boolean val = this.componentValues[this.baseToTransition[id]] < 0;
			activeStates.set(id, val);
			if (val) state.add(this.baseToSentence[id]);
		}

		System.out.println("INITIAL STATE VALUES: " + state);
		if (this.initID != -1) forwardprop_wrapper(this.initID, false);
		if (this.initID != -1) this.propnet.getInitProposition().setValue(true);
		return new MachineState(state, activeStates);
	}

	@Override
	public List<Move> getLegalMoves(MachineState state, Role role) throws MoveDefinitionException {
		BitSet b = state.getPropContents();
		for (int i = 0; i < this.numberOfBaseProps; i++) forwardprop_wrapper(i, b.get(i));
		Proposition[] legalProps = this.legalPropositions.get(role);
		ArrayList<Move> moves = new ArrayList<Move>();
		for (Proposition p : legalProps) {
			if ((this.componentValues[p.componentId] < 0)) moves.add(this.getMoveFromProposition(p));
		}
//		System.out.println("Legal Moves: " + moves);
		return moves;
	}

	@Override
	public MachineState getNextState(MachineState state, List<Move> moves) throws TransitionDefinitionException {
//		System.out.println("HERE WE GO");
		BitSet b = state.getPropContents(), in = this.markactions(moves);
//		System.out.println("---");
		for (int i = 0; i < this.numberOfBaseProps; i++) {
//			if (b.get(i)) System.out.println("BASE ON: " + i);
			forwardprop_wrapper(i, b.get(i));
		}
		for (int i = this.inputOffset; i < this.inputOffset + this.numberOfInputProps; i++) {
//			if (in.get(i)) System.out.println("INPUT ON: " + i);
			forwardprop_wrapper(i, in.get(i));
		}
//		for (Component c : this.propnet.getComponents()) c.setPreviousValue(c.getValue());

		Set<GdlSentence> gdlState = new HashSet<GdlSentence>();
		BitSet activeStates = new BitSet(this.numberOfBaseProps);
		for (int id = 0; id < this.numberOfBaseProps; id++) {
			boolean val = this.componentValues[this.baseToTransition[id]] < 0;
			activeStates.set(id, val);
			if (val) gdlState.add(this.baseToSentence[id]);
		}
//		System.out.println("NEXT STATE VALUES: " + gdlState);

		MachineState nextState = new MachineState(gdlState, activeStates);

//		System.out.println("" + state + " + " + moves + " = " + nextState);
//		System.out.println("---");

		return nextState;
	}

	// ----------------------------------------------

	private void forwardprop_wrapper(int componentid, boolean b) {
		if (b) forwardprop(componentid, 0xFFFFFFFF);
		else forwardprop(componentid, 0);
//		if (b) forwardprop(componentid, 0x80000000);
//		else forwardprop(componentid, 0x7FFFFFFF);
	}

//	private void forwardprop(Component c) {
//		boolean c_val = c.getValue();
//		if (c_val == c.previousValue()) return;
//		c.setPreviousValue(c_val);
//		if ((c instanceof Transition)) return;
//		for (Component o : c.fasterGetOutputs()) {
//			if ((o instanceof Proposition)) {
//				o.setPreviousValue(o.getValue());
//				((Proposition) o).setValue(c_val);
//			}
//			else if ((o instanceof And)) ((And) o).counter += (c_val) ? 1 : -1;
//			else if ((o instanceof Or)) ((Or) o).counter += (c_val) ? 1 : -1;
//			else if ((o instanceof Transition)) {
//				o.setPreviousValue(o.getValue());
//				((Transition) o).setValue(c_val);
//			}
//			forwardprop(o);
//		}
//	}

	private void forwardprop(int componentid, int currentValue) {
		boolean c_val = (currentValue < 0);
//		if (componentid == this.terminalID) {
//			System.out.println("Prop to Terminal ID with new_val: " + c_val);
//		}
		if (componentid < 0) { // transition
			this.componentValues[-componentid] = currentValue;
			return;
		}
		boolean prevValue = (this.componentValues[componentid] < 0);
		boolean isNot = (componentid >= this.notStart && componentid < this.notEnd);
		if (isNot) {
			if (prevValue == c_val) return;
			this.componentValues[componentid] = currentValue;
		} else {
			this.componentValues[componentid] = currentValue;
			if (prevValue == c_val) return;
		}
		int num_loc = this.componentMetadata[componentid];
		int num = num_loc >>> 16;//(num_loc & 0xFFFF0000) >>> 16;
		int loc = (num_loc & 0xFFFF);
		for (int i = loc; i < num + loc; i++) {
			int c = this.componentConnectivity[i], value = 0;
			if (c < this.numberOfPropositions) value = currentValue;
			else value = this.componentValues[c] + ((c_val) ? 1 : -1);
			forwardprop(c, value);
		}
	}

	private BitSet markactions(List<Move> moves) {
		BitSet b = new BitSet(this.numberOfBaseProps + this.numberOfInputProps);
		GdlSentence[] gdlMoves = toDoes(moves);
		for (GdlSentence m : gdlMoves) {
			int id = this.propnet.getInputPropositions().get(m).componentId;
			b.set(id);
		}
		return b;
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
