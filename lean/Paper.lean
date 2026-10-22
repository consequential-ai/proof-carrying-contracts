import PC2

/-!
# The paper and its mechanization

Every numbered definition, assumption and result of "Proof-Carrying Contracts: Commitments AI Agents
Cannot Break", with the Lean declaration that states it. For each theorem, the axioms it depends on
are checked at build time: the build fails if any of them changes, so no result depends on `sorry` or
on an axiom beyond Lean's standard ones (`propext`, `Classical.choice`, `Quot.sound`).

Assumptions are hypotheses of the theorems that use them: each theorem's signature lists exactly what it
assumes.
-/

/-! ## §3 The architecture -/

-- Definition 1 (Tool)
#guard_msgs (drop info) in
#check @PC2.Tool

-- Eqs. (1)–(3): enabledness, daemonic control, admissibility = wp
#guard_msgs (drop info) in
#check @PC2.Tool.adm_iff
/-- info: 'PC2.Tool.adm_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.Tool.adm_iff

-- §3.5.2 The precondition construction
#guard_msgs (drop info) in
#check @PC2.Tool.adm_restrict
/-- info: 'PC2.Tool.adm_restrict' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.Tool.adm_restrict

-- Definition 2 (Contract)
#guard_msgs (drop info) in
#check @PC2.Contract

-- Definition 3 (Obligation)
#guard_msgs (drop info) in
#check @PC2.Contract.Obl

-- Definition 4 (Delayed obligation) and its window
#guard_msgs (drop info) in
#check @PC2.Contract.OblN

-- §3.3 With n = 0 the delayed obligation is the obligation
#guard_msgs (drop info) in
#check @PC2.Contract.oblN_zero
/-- info: 'PC2.Contract.oblN_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.Contract.oblN_zero

-- Example 1 (the standard contract)
#guard_msgs (drop info) in
#check @PC2.Standard.Spec.contract

-- Example 1: A3 for every contract built on the template
#guard_msgs (drop info) in
#check @PC2.Standard.Spec.cert
/-- info: 'PC2.Standard.Spec.cert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.Standard.Spec.cert

-- Algorithm 1 (the Airlock) and Algorithm 2 (proof checking)
#guard_msgs (drop info) in
#check @PC2.Next

-- Algorithm 1, line 6: what the agent's channel gives
#guard_msgs (drop info) in
#check @PC2.Input

-- Algorithm 2, check
#guard_msgs (drop info) in
#check @PC2.checkOK

-- §3.5.2 Settlement obligation
#guard_msgs (drop info) in
#check @PC2.Contract.settle_obligation_zero
/-- info: 'PC2.Contract.settle_obligation_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PC2.Contract.settle_obligation_zero

-- §3.5.2 Settlement when the view determines the goal
#guard_msgs (drop info) in
#check @PC2.Contract.settle_obligation_view
/-- info: 'PC2.Contract.settle_obligation_view' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PC2.Contract.settle_obligation_view

-- §3.5.2 The communication tool
#guard_msgs (drop info) in
#check @PC2.send_adm
/-- info: 'PC2.send_adm' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.send_adm


/-! ## §4 Guarantees -/

-- A1 (Sound checking)
#guard_msgs (drop info) in
#check @PC2.Checker.Sound

-- A2 (Coverage)
#guard_msgs (drop info) in
#check @PC2.Coverage

-- A3 (Initialization and control), checked at startup
#guard_msgs (drop info) in
#check @PC2.Contract.Cert

-- A4 (Execution integrity): the executions of Algorithms 1–2
#guard_msgs (drop info) in
#check @PC2.Execution

-- A4 (iii) follows from Algorithms 1–2
#guard_msgs (drop info) in
#check @PC2.call_discipline
/-- info: 'PC2.call_discipline' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.call_discipline

-- Lemma 1 (Window)
#guard_msgs (drop info) in
#check @PC2.window
/-- info: 'PC2.window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.window

-- Theorem 1 (Anytime compliance to the contract)
#guard_msgs (drop info) in
#check @PC2.anytime_compliance
/-- info: 'PC2.anytime_compliance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PC2.anytime_compliance

-- Standard form (Example 1)
#guard_msgs (drop info) in
#check @PC2.StandardForm

-- Theorem 2 (Completion)
#guard_msgs (drop info) in
#check @PC2.completion
/-- info: 'PC2.completion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PC2.completion

-- Proposition 1 (What settlement asks)
#guard_msgs (drop info) in
#check @PC2.Contract.settle_obligation
/-- info: 'PC2.Contract.settle_obligation' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.Contract.settle_obligation

-- Proposition 1 for the standard contract
#guard_msgs (drop info) in
#check @PC2.Standard.Spec.settle_obligation
/-- info: 'PC2.Standard.Spec.settle_obligation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.Standard.Spec.settle_obligation

-- §4.2 No veto over an authorized settlement
#guard_msgs (drop info) in
#check @PC2.no_veto
/-- info: 'PC2.no_veto' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PC2.no_veto


/-! ## §5 From compliance to safety -/

-- A5 (Fidelity)
#guard_msgs (drop info) in
#check @PC2.Fidelity

-- A6 (Adequacy)
#guard_msgs (drop info) in
#check @PC2.Adequacy

-- A6 (Adequacy), goal part
#guard_msgs (drop info) in
#check @PC2.GoalAdequacy

-- Theorem 3 (World safety)
#guard_msgs (drop info) in
#check @PC2.world_safety
/-- info: 'PC2.world_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PC2.world_safety

-- Corollary 4 (Completion in the world)
#guard_msgs (drop info) in
#check @PC2.completion_in_world
/-- info: 'PC2.completion_in_world' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PC2.completion_in_world

-- A7 (Isolation of the agent), as stated in §5.2
#guard_msgs (drop info) in
#check @PC2.System.A7

-- The stepwise isolation of App. G, (NI1) and (NI2)
#guard_msgs (drop info) in
#check @PC2.System.Isolation

-- Lemma 2 (Isolation)
#guard_msgs (drop info) in
#check @PC2.System.isolation
/-- info: 'PC2.System.isolation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.System.isolation

-- Coverage for every agent, from reference executions
#guard_msgs (drop info) in
#check @PC2.System.coverage_of_ref
/-- info: 'PC2.System.coverage_of_ref' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.System.coverage_of_ref

-- Fidelity for every agent, from reference executions
#guard_msgs (drop info) in
#check @PC2.System.fidelity_of_ref
/-- info: 'PC2.System.fidelity_of_ref' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.System.fidelity_of_ref

-- Theorem 5 (1) Anytime safety, for every agent
#guard_msgs (drop info) in
#check @PC2.guarantees
/-- info: 'PC2.guarantees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PC2.guarantees

-- Theorem 5 (2)–(3) Settlement and termination, for every agent
#guard_msgs (drop info) in
#check @PC2.guarantees_standard
/-- info: 'PC2.guarantees_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PC2.guarantees_standard

-- Theorem 5 (4) Deadline, for every agent
#guard_msgs (drop info) in
#check @PC2.guarantees_deadline
/-- info: 'PC2.guarantees_deadline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PC2.guarantees_deadline


/-! ## §6 Composing capabilities -/

-- Definition 5 (Capability module)
#guard_msgs (drop info) in
#check @PC2.Module

-- Paired tools (Eq. product-model)
#guard_msgs (drop info) in
#check @PC2.tensor

-- Compatibility of effects (Eq. no-coupling)
#guard_msgs (drop info) in
#check @PC2.Compatible

-- Definition 7 (Extension)
#guard_msgs (drop info) in
#check @PC2.Module.ext

-- Proposition 2 (Custody)
#guard_msgs (drop info) in
#check @PC2.custody_guarantees
/-- info: 'PC2.custody_guarantees' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.custody_guarantees

-- Proposition 3 (Formal interface)
#guard_msgs (drop info) in
#check @PC2.interface_guarantees
/-- info: 'PC2.interface_guarantees' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.interface_guarantees

-- Proposition 4 (Domain invariant)
#guard_msgs (drop info) in
#check @PC2.domain_invariant
/-- info: 'PC2.domain_invariant' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.domain_invariant

-- Theorem 6 (From local to global guarantees), coverage
#guard_msgs (drop info) in
#check @PC2.local_to_global_cov
/-- info: 'PC2.local_to_global_cov' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.local_to_global_cov

-- Theorem 6, fidelity
#guard_msgs (drop info) in
#check @PC2.local_to_global_fid
/-- info: 'PC2.local_to_global_fid' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.local_to_global_fid

-- Theorem 6 for a contract built from modules
#guard_msgs (drop info) in
#check @PC2.Composite.local_to_global
/-- info: 'PC2.Composite.local_to_global' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.Composite.local_to_global

-- Theorem 6 for a contract built from modules, fidelity
#guard_msgs (drop info) in
#check @PC2.Composite.local_to_global_fidelity
/-- info: 'PC2.Composite.local_to_global_fidelity' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.Composite.local_to_global_fidelity

-- §6.4 A precondition keeps coverage
#guard_msgs (drop info) in
#check @PC2.cov_restrict
/-- info: 'PC2.cov_restrict' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.cov_restrict

-- §6.4 A precondition keeps fidelity
#guard_msgs (drop info) in
#check @PC2.fid_restrict
/-- info: 'PC2.fid_restrict' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.fid_restrict

-- §6.4 Checking an extension
#guard_msgs (drop info) in
#check @PC2.ext_retained
/-- info: 'PC2.ext_retained' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.ext_retained


/-! ## Appendix A -/

-- Eq. (A.1)
#guard_msgs (drop info) in
#check @PC2.Contract.oblN_wp
/-- info: 'PC2.Contract.oblN_wp' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.Contract.oblN_wp

-- Proposition A.1 (The most permissive safe gate)
#guard_msgs (drop info) in
#check @PC2.Contract.most_permissive_gate
/-- info: 'PC2.Contract.most_permissive_gate' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.Contract.most_permissive_gate

-- Proposition A.1, decidable gates
#guard_msgs (drop info) in
#check @PC2.Contract.decidable_gate
/-- info: 'PC2.Contract.decidable_gate' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.Contract.decidable_gate

-- The policy-engine example
#guard_msgs (drop info) in
#check @PC2.policy_engine_example
/-- info: 'PC2.policy_engine_example' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.policy_engine_example


/-! ## Appendix C -/

-- Control design: the certificate from the design
#guard_msgs (drop info) in
#check @PC2.Design.cert
/-- info: 'PC2.Design.cert' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PC2.Design.cert

-- The compute budget
#guard_msgs (drop info) in
#check @PC2.ComputeBudget.sound
/-- info: 'PC2.ComputeBudget.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.ComputeBudget.sound


/-! ## Appendix D -/

-- Extended tools include the original model
#guard_msgs (drop info) in
#check @PC2.extend_mono
/-- info: 'PC2.extend_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.extend_mono

-- Extended tools are enabled where the original ones are
#guard_msgs (drop info) in
#check @PC2.extend_en
/-- info: 'PC2.extend_en' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.extend_en

-- Extension commutes with preconditions
#guard_msgs (drop info) in
#check @PC2.extend_restrict
/-- info: 'PC2.extend_restrict' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.extend_restrict

-- No gap: T' = T
#guard_msgs (drop info) in
#check @PC2.extend_zero
/-- info: 'PC2.extend_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.extend_zero


/-! ## Appendix E -/

-- Proposition E.1 (Preserving budget correspondence)
#guard_msgs (drop info) in
#check @PC2.budget_correspondence
/-- info: 'PC2.budget_correspondence' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.budget_correspondence

-- Proposition E.1: the first line of A5
#guard_msgs (drop info) in
#check @PC2.ledger_fidelity
/-- info: 'PC2.ledger_fidelity' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.ledger_fidelity

-- Adequacy for the budget
#guard_msgs (drop info) in
#check @PC2.budget_adequacy
/-- info: 'PC2.budget_adequacy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.budget_adequacy

-- The bound after closing (Eq. post-closing budget)
#guard_msgs (drop info) in
#check @PC2.budget_after_closing
/-- info: 'PC2.budget_after_closing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.budget_after_closing

-- Proposition E.2 (Preserving booking correspondence)
#guard_msgs (drop info) in
#check @PC2.booking_correspondence
/-- info: 'PC2.booking_correspondence' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.booking_correspondence

-- From a recorded confirmation to a held reservation
#guard_msgs (drop info) in
#check @PC2.booking_goal
/-- info: 'PC2.booking_goal' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.booking_goal


/-! ## Appendix F -/

-- What goes wrong without isolation
#guard_msgs (drop info) in
#check @PC2.ungated_unsafe
/-- info: 'PC2.ungated_unsafe' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.ungated_unsafe


/-! ## Appendix G -/

-- A7 as stated implies (NI1) and (NI2)
#guard_msgs (drop info) in
#check @PC2.System.A7.isolation
/-- info: 'PC2.System.A7.isolation' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.System.A7.isolation

-- Lemma G.1 (Isolation, stepwise formulation)
#guard_msgs (drop info) in
#check @PC2.isolation_stepwise
/-- info: 'PC2.isolation_stepwise' does not depend on any axioms -/
#guard_msgs in
#print axioms PC2.isolation_stepwise


/-! ## The travel contract (Table 1) and Fig. 2 -/

-- The travel contract satisfies A3
#guard_msgs (drop info) in
#check @PC2.Travel.cert
/-- info: 'PC2.Travel.cert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.Travel.cert

-- Episode 1: booking the unrated partner hotel is rejected
#guard_msgs (drop info) in
#check @PC2.Travel.ep1_book_rejected
/-- info: 'PC2.Travel.ep1_book_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PC2.Travel.ep1_book_rejected

-- Episode 1: asking the expert is admissible
#guard_msgs (drop info) in
#check @PC2.Travel.ep1_rate
/-- info: 'PC2.Travel.ep1_rate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.Travel.ep1_rate

-- Episode 1: asking again returns the recorded rating
#guard_msgs (drop info) in
#check @PC2.Travel.ep1_rate_again
/-- info: 'PC2.Travel.ep1_rate_again' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PC2.Travel.ep1_rate_again

-- Episode 2: booking Aurora for 900 is admissible
#guard_msgs (drop info) in
#check @PC2.Travel.ep2_book
/-- info: 'PC2.Travel.ep2_book' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.Travel.ep2_book

-- Episode 3: downloading mail is admissible
#guard_msgs (drop info) in
#check @PC2.Travel.ep3_download
/-- info: 'PC2.Travel.ep3_download' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.Travel.ep3_download

-- Episode 3: the injected recipient is rejected
#guard_msgs (drop info) in
#check @PC2.Travel.ep3_injection_rejected
/-- info: 'PC2.Travel.ep3_injection_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PC2.Travel.ep3_injection_rejected

-- Episode 4: settling before the goal is rejected
#guard_msgs (drop info) in
#check @PC2.Travel.ep4_premature
/-- info: 'PC2.Travel.ep4_premature' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PC2.Travel.ep4_premature

-- Episode 4: settling once the goal holds is admissible
#guard_msgs (drop info) in
#check @PC2.Travel.ep4_settle
/-- info: 'PC2.Travel.ep4_settle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PC2.Travel.ep4_settle

