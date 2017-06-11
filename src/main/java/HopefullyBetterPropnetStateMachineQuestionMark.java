import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlDistinct;
import org.ggp.base.util.gdl.grammar.GdlFunction;
import org.ggp.base.util.gdl.grammar.GdlLiteral;
import org.ggp.base.util.gdl.grammar.GdlPool;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlRule;
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
import org.ggp.base.util.propnet.factory.LegacyPropNetFactory;
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

	public PropNet propnet;
	private List<Role> roles;
	private Proposition[] basePropositions;
	private Proposition[] inputPropositions;
	private ArrayList<Map<GdlTerm, GdlSentence>> inputMap;
	private Map<Role, Proposition[]> legalPropositions;
	public List<Gdl> description;

	private boolean factoringEnabled = false;
	public boolean zeroSum = true;

	@Override
	public List<Move> findActions(Role role) throws MoveDefinitionException {
		Set<Proposition> legalProps = this.propnet.getLegalPropositions().get(role);
		ArrayList<Move> legalMoves = new ArrayList<Move>();
		for (Proposition p : legalProps) {
			legalMoves.add(this.getMoveFromProposition(p));
		}
		return legalMoves;
	}

	private void bfs(Component c) {
		if (c.connectedToTerminal) return;
		c.connectedToTerminal = true;
		for (Component cc : c.getInputs()) bfs(cc);
	}

	private void sanitizeDistinctHelper(Gdl gdl, List<Gdl> in, List<Gdl> out) {
	    if (!(gdl instanceof GdlRule)) {
	        out.add(gdl);
	        return;
	    }
	    GdlRule rule = (GdlRule) gdl;
	    for (GdlLiteral lit : rule.getBody()) {
	        if (lit instanceof GdlDistinct) {
	            GdlDistinct d = (GdlDistinct) lit;
	            GdlTerm a = d.getArg1();
	            GdlTerm b = d.getArg2();
	            if (!(a instanceof GdlFunction) && !(b instanceof GdlFunction)) continue;
	            if (!(a instanceof GdlFunction && b instanceof GdlFunction)) return;
	            GdlSentence af = ((GdlFunction) a).toSentence();
	            GdlSentence bf = ((GdlFunction) b).toSentence();
	            if (!af.getName().equals(bf.getName())) return;
	            if (af.arity() != bf.arity()) return;
	            for (int i = 0; i < af.arity(); i++) {
	                List<GdlLiteral> ruleBody = new ArrayList<>();
	                for (GdlLiteral newLit : rule.getBody()) {
	                    if (newLit != lit) ruleBody.add(newLit);
	                    else ruleBody.add(GdlPool.getDistinct(af.get(i), bf.get(i)));
	                }
	                GdlRule newRule = GdlPool.getRule(rule.getHead(), ruleBody);
	                in.add(newRule);
	            }
	            return;
	        }
	    }
	    for (GdlLiteral lit : rule.getBody()) {
	        if (lit instanceof GdlDistinct) {
	            break;
	        }
	    }
	    out.add(rule);
	}

	private List<Gdl> sanitizeDistinct(List<Gdl> description) {
	    List<Gdl> out = new ArrayList<>();
	    for (int i = 0; i < description.size(); i++) {
	        sanitizeDistinctHelper(description.get(i), description, out);
	    }
	    return out;
	}

	private void resetall() {
		for (Component c : this.propnet.getComponents()) c.connectedToTerminal = false;
	}

	@Override
	public void initialize(List<Gdl> description) {
		description = sanitizeDistinct(description);
		this.description = description;

		// create propnet
		try {
			this.propnet = OptimizingPropNetFactory.create(description);
		} catch (Exception e) {
			this.propnet = LegacyPropNetFactory.create(description);
		}
		System.out.println("[PROPNET] Finished Building Propnet");

		for (Role r : this.propnet.getRoles()) {
			for (Proposition p : this.propnet.getGoalPropositions().get(r)) {
				if (this.getGoalValue(p) != 0 && this.getGoalValue(p) != 100 && this.getGoalValue(p) != 50) {
					this.zeroSum = false;
				}
			}
			if (!this.zeroSum) break;
		}

		// check zero-sum
		if (this.zeroSum) System.out.println("[PROPNET] This Game is Zero-Sum");
		else System.out.println("[PROPNET] This Game is NOT Zero-Sum");

		// mark input/bases
		for (Proposition p : this.propnet.getInputPropositions().values()) p.setInput(true);
		for (Proposition p : this.propnet.getBasePropositions().values()) p.setBase(true);
		for (Role r : this.propnet.getRoles()) {
			for (Proposition p : this.propnet.getLegalPropositions().get(r)) p.setLegal(true);
			for (Proposition p : this.propnet.getGoalPropositions().get(r))  p.setGoal(true);
		}

		// optimization
		System.out.println("[PROPNET] Begin Optimizing View Propositions");
		int numberTrimmed = 0;
		Set<Proposition> propsToRemove = new HashSet<>();
		for (Proposition p : this.propnet.getPropositions()) {
			if (p.isBase() || p.isInput() || p.isGoal() || p.isLegal()) continue;
			else if (p.equals(this.propnet.getInitProposition())) continue;
			else if (p.equals(this.propnet.getTerminalProposition())) continue;
			else if (this.propnet.getLegalInputMap().get(p) != null) continue;
			else {
				if (p.getInputs().size() == 1 && p.getOutputs().size() == 1) {
					Component inputComp = p.getSingleInput();
					Component outputComp = p.getSingleOutput();
					inputComp.removeOutput(p);
					outputComp.removeInput(p);
					inputComp.addOutput(outputComp);
					outputComp.addInput(inputComp);
					propsToRemove.add(p);
					numberTrimmed++;
				}
			}
		}
		for (Proposition p : propsToRemove) this.propnet.removeComponent(p);
		System.out.println("[PROPNET] Trimmed " + numberTrimmed + " View Propositions");


		// do some bs factoring
//		System.out.println("[PROPNET] Terminal Inputs: " + this.propnet.getTerminalProposition().getSingleInput().getInputs().size());
//		bfs(this.propnet.getTerminalProposition());
//		ArrayList<Component> toRemove = new ArrayList<>();
//			for (Proposition p : this.propnet.getBasePropositions().values()) {
//				if (!p.connectedToTerminal) toRemove.add(p);
//			}
//		int tempNumberOfTotalInputs = this.propnet.getInputPropositions().size();
//		System.out.println("Total # of Legals: " + this.propnet.getInputPropositions().size());
//		if (this.propnet.getRoles().size() == 1) {
//			for (Proposition p : this.propnet.getInputPropositions().values()) {
//				if (!p.connectedToTerminal) {
//					toRemove.add(this.propnet.getLegalInputMap().get(p));
//				}
//			}
//
//			if (toRemove.size() == 0) { // best buttons
//				Component or = this.propnet.getTerminalProposition().getSingleInput();
//				if ((or instanceof Or)) {
//					for (Component c : or.getInputs()) {
//						resetall();
//						bfs(c);
//
//						for (Proposition p : this.propnet.getInputPropositions().values()) {
//							if (!p.connectedToTerminal) {
//								toRemove.add(this.propnet.getLegalInputMap().get(p));
//							}
//						}
//
//						if (toRemove.size() != tempNumberOfTotalInputs) break;
//						else {
//							toRemove.clear();
//						}
//					}
//				}
//			}

//			if (toRemove.size() == 0) { // another attempt
//				for (Component c : this.propnet.getInputPropositions().values()) c.setInput(true);
//				for (Component c : this.propnet.getBasePropositions().values()) c.setBase(true);
//				Component or = this.propnet.getTerminalProposition().getSingleInput();
//				if ((or instanceof Or)) {
//					for (Component c : or.getInputs()) {
//						resetall();
//						Set<Component> comps = new HashSet<>();
//						this.connectedBases(c, comps);
//
//						System.out.println("Connected BASES: " + comps);
//
//						for (Component cc : comps) if (cc.isBase()) System.out.println("well, I am a base");
//						for (Component cc : comps) findConnectedInputs(cc.getSingleInput(), cc);
//
//						for (Proposition p : this.propnet.getInputPropositions().values()) {
//							if (!p.connectedToTerminal) {
//								toRemove.add(this.propnet.getLegalInputMap().get(p));
//							}
//						}
//
//						if (toRemove.size() != tempNumberOfTotalInputs) break;
//						else {
//							if (toRemove.size() == tempNumberOfTotalInputs) System.out.println("oops");
//							toRemove.clear();
//						}
//					}
//				}
//			}
//
//			System.out.println("Removing #: " + toRemove.size());
//			for (Component p : toRemove) {
//				System.out.println("REMOVING: " + p);
//				p.toIgnore = true;
//				// this.propnet.removeComponent(p);
//			}
//			for (Component p : this.propnet.getInputPropositions().values()) {
//				Component c = this.propnet.getLegalInputMap().get(p);
//				if (!c.toIgnore) System.out.println("REMAINING: " + c);
//			}
//		}

		// more optimizations + crystalization
		this.roles = propnet.getRoles();
		for (Component c : this.propnet.getComponents()) c.crystalize();
		this.basePropositions = new Proposition[this.propnet.getBasePropositions().size()];
		this.inputPropositions = new Proposition[this.propnet.getInputPropositions().size()];
		this.legalPropositions = new HashMap<>();

		for (Component c : this.propnet.getComponents()) {
			if ((c instanceof Constant)) c.setPreviousValue(!c.getValue());
			else c.setPreviousValue(false);
		}

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
		//this.propnet.renderToFile("C:\\Users\\panch\\Desktop\\knightstour.dot");
		System.out.println("Finished Initializing StateMachine");
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
		return this.propnet.getTerminalProposition().getValue();
//		for (Component c : this.propnet.getTerminalProposition().fasterGetInputs()) {
//			if (!c.getValue()) return false;
//		}
//
//		return true;
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
		for (Component c : this.propnet.getComponents()) if ((c instanceof Constant)) forwardprop(c);
		Proposition initProp = this.propnet.getInitProposition();
		if (initProp != null) {
			this.propnet.getInitProposition().setValue(true);
			for (Component c : this.propnet.getComponents()) if ((c instanceof Not)) forwardprop(c);
			forwardprop(this.propnet.getInitProposition());
		}

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
		if (initProp != null) {
			this.propnet.getInitProposition().setValue(false);
			forwardprop(this.propnet.getInitProposition());
			System.out.println("Turning off init prop...");
		}
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
//			if (this.factoringEnabled && p.toIgnore) continue;
			if (p.getValue()) moves.add(this.getMoveFromProposition(p));
		}
//		if (moves.size() == 0 && this.factoringEnabled) { // LOL
//			this.factoringEnabled = false;
//			System.out.println("FACTORING IS NOW OFF");
//			for (Proposition p : legalProps) {
//				if (this.factoringEnabled && p.toIgnore) continue;
//				if (p.getValue()) moves.add(this.getMoveFromProposition(p));
//			}
//		}
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
//			if (activeBits.get(i)) {
//				System.out.println("True: " + this.basePropositions[i].getName());
//			}
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
