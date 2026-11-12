(** * The paper and its mechanization

Every numbered definition, assumption and result of "Proof-Carrying Contracts:
Commitments AI Agents Cannot Break", with the Rocq declaration that states it.
For each theorem, [Print Assumptions] lists what it depends on; [make] checks
that every one of them prints "Closed under the global context": no result
depends on an axiom or on an admitted lemma.

Assumptions are hypotheses of the theorems that use them: each theorem's
statement lists exactly what it assumes. *)

From PC2 Require Import All.

Import Contract.

(** ** §3 The architecture *)

(* Definition 1 (Tool) *)
Check @Tool.t.

(* Eqs. (1)–(3): enabledness, daemonic control, admissibility = wp *)
Check @Tool.adm_iff.
Print Assumptions Tool.adm_iff.

(* §3.5.2 The precondition construction *)
Check @Tool.adm_restrict.
Print Assumptions Tool.adm_restrict.

(* Definition 2 (Contract) *)
Check @Contract.t.

(* Definition 3 (Obligation) *)
Check @Contract.Obl.

(* Definition 4 (Delayed obligation) and its window *)
Check @Contract.OblN.

(* §3.3 With n = 0 the delayed obligation is the obligation *)
Check @Contract.oblN_zero.
Print Assumptions Contract.oblN_zero.

(* Example 1 (the standard contract) *)
Check @Standard.Spec.contract.

(* Example 1: the clause, while the contract is ongoing *)
Check @Standard.Spec.CP.
Print Assumptions Standard.Spec.CP.

(* Example 1: A3 for every contract built on the template *)
Check @Standard.Spec.cert.
Print Assumptions Standard.Spec.cert.

(* Algorithm 1 (the Airlock) and Algorithm 2 (proof checking) *)
Check @Next.

(* Algorithm 1, line 6: what the agent's channel gives *)
Check @Input.

(* Algorithm 2, check, a test, and what it says *)
Check @checkOK.
Check @checkOKP.
Print Assumptions checkOKP.

(* §3.5.2 Settlement obligation *)
Check @settle_obligation_zero.
Print Assumptions settle_obligation_zero.

(* §3.5.2 Settlement when the view determines the goal *)
Check @settle_obligation_view.
Print Assumptions settle_obligation_view.

(* §3.5.2 The communication tool *)
Check @send_adm.
Print Assumptions send_adm.

(** ** §4 Compliance and completion *)

(* A1 (Sound checking) *)
Check @Checker.Sound.

(* A2 (Coverage) *)
Check @Coverage.

(* A3 (Initialization and control), checked at startup *)
Check @Contract.Cert.

(* A4 (Execution integrity): the executions of Algorithms 1–2 *)
Check @Execution.

(* A4 (iii) follows from Algorithms 1–2 *)
Check @call_discipline.
Print Assumptions call_discipline.

(* Lemma 1 (Window) *)
Check @window.
Print Assumptions window.

(* Theorem 1 (Anytime compliance to the contract) *)
Check @anytime_compliance.
Print Assumptions anytime_compliance.

(* Standard form (Example 1) *)
Check @StandardForm.t.

(* Theorem 2 (Completion) *)
Check @completion.
Print Assumptions completion.

(* Proposition 1 (What settlement asks) *)
Check @settle_obligation.
Print Assumptions settle_obligation.

(* Proposition 1 for the standard contract *)
Check @Standard.Spec.settle_obligation.
Print Assumptions Standard.Spec.settle_obligation.

(* §4.2 No veto over an authorized settlement *)
Check @no_veto.
Print Assumptions no_veto.

(** ** §5 From compliance to safety *)

(* A5 (Fidelity) *)
Check @Fidelity.

(* A6 (Adequacy) *)
Check @Adequacy.

(* A6 (Adequacy), goal part *)
Check @GoalAdequacy.

(* Theorem 3 (World safety) *)
Check @world_safety.
Print Assumptions world_safety.

(* Corollary 4 (Completion in the world) *)
Check @completion_in_world.
Print Assumptions completion_in_world.

(* A7 (Isolation of the agent), as stated in §5.2 *)
Check @System.A7.

(* The stepwise isolation of App. G, (NI1) and (NI2) *)
Check @System.Isolation.

(* Lemma 2 (Isolation) *)
Check @System.isolation.
Print Assumptions System.isolation.

(* Coverage for every agent, from reference executions *)
Check @System.coverage_of_ref.
Print Assumptions System.coverage_of_ref.

(* Fidelity for every agent, from reference executions *)
Check @System.fidelity_of_ref.
Print Assumptions System.fidelity_of_ref.

(* Coverage and fidelity for every agent, from A7 as stated in §5.2 *)
Check @System.coverage_of_A7.
Print Assumptions System.coverage_of_A7.
Check @System.fidelity_of_A7.
Print Assumptions System.fidelity_of_A7.

(* Theorem 5 (1) Anytime safety, for every agent *)
Check @guarantees.
Print Assumptions guarantees.

(* Theorem 5 (2)–(3) Settlement and termination, for every agent *)
Check @guarantees_standard.
Print Assumptions guarantees_standard.

(* Theorem 5 (4) Deadline, for every agent *)
Check @guarantees_deadline.
Print Assumptions guarantees_deadline.

(** ** §6 Capability modules *)

(* Definition 5 (Capability module) *)
Check @CapModule.t.

(* Paired tools (Eq. product-model) *)
Check @tensor.

(* Compatibility of effects (Eq. no-coupling) *)
Check @Compatible.

(* Definition 7 (Extension) *)
Check @ext.

(* §6.3 The custody module (Eq. custody-module) *)
Check @custody.

(* §6.3 The formal-interface module (Eq. interface-module) *)
Check @interface.

(* Proposition 2 (Custody) *)
Check @custody_guarantees.
Print Assumptions custody_guarantees.

(* Proposition 3 (Formal interface) *)
Check @interface_guarantees.
Print Assumptions interface_guarantees.

(* Proposition 4 (Domain invariant) *)
Check @domain_invariant.
Print Assumptions domain_invariant.

(* Theorem 6 (From local to global guarantees), coverage *)
Check @local_to_global_cov.
Print Assumptions local_to_global_cov.

(* Theorem 6, fidelity *)
Check @local_to_global_fid.
Print Assumptions local_to_global_fid.

(* Theorem 6 for a contract built from modules *)
Check @Composite.local_to_global.
Print Assumptions Composite.local_to_global.

(* Theorem 6 for a contract built from modules, fidelity *)
Check @Composite.local_to_global_fidelity.
Print Assumptions Composite.local_to_global_fidelity.

(* §6.4 A precondition keeps coverage *)
Check @cov_restrict.
Print Assumptions cov_restrict.

(* §6.4 A precondition keeps fidelity *)
Check @fid_restrict.
Print Assumptions fid_restrict.

(* §6.4 Checking an extension *)
Check @ext_retained.
Print Assumptions ext_retained.

(** ** Appendix A: the obligation as a weakest precondition *)

(* What the agent knows, K_n(v) *)
Check @ContractWP.Kn.

(* Safe gates *)
Check @ContractWP.SafeGate.

(* Eq. (A.1) *)
Check @ContractWP.oblN_wp.
Print Assumptions ContractWP.oblN_wp.

(* Proposition A.1 (The most permissive safe gate) *)
Check @ContractWP.most_permissive_gate.
Print Assumptions ContractWP.most_permissive_gate.

(* Proposition A.1, decidable gates *)
Check @ContractWP.decidable_gate.
Print Assumptions ContractWP.decidable_gate.

(* The policy-engine example *)
Check @policy_engine_example.
Print Assumptions policy_engine_example.

(** ** Appendix C: a design for the control step *)

(* A control design, its routine, and the conditions of App. C *)
Check @Design.t.
Check @Design.model.
Check @Design.Sound.

(* Control design: the certificate from the design *)
Check @Design.cert.
Print Assumptions Design.cert.

(* The compute-budget contract and its design *)
Check @ComputeBudget.contract.
Check @ComputeBudget.design.

(* Its clause and its models, as tests, and what they say *)
Check @ComputeBudget.CP.
Print Assumptions ComputeBudget.CP.
Check @ComputeBudget.idleP.
Print Assumptions ComputeBudget.idleP.
Check @ComputeBudget.shutP.
Print Assumptions ComputeBudget.shutP.

(* The compute budget *)
Check @ComputeBudget.sound.
Print Assumptions ComputeBudget.sound.

(** ** Appendix D: time between operations *)

(* The extended tool T' and the extended contract K' *)
Check @extend.
Check @extendK.

(* Extended tools include the original model *)
Check @extend_mono.
Print Assumptions extend_mono.

(* Extended tools are enabled where the original ones are *)
Check @extend_en.
Print Assumptions extend_en.

(* Extension commutes with preconditions *)
Check @extend_restrict.
Print Assumptions extend_restrict.

(* No gap: T' = T *)
Check @extend_zero.
Print Assumptions extend_zero.

(** ** Appendix E: two worked examples of correspondence *)

(* The ledger's correspondence and the reservation discipline *)
Check @ledgerρ.
Check @Reservation.
Check @ServiceCond.

(* Proposition E.1 (Preserving budget correspondence) *)
Check @budget_correspondence.
Print Assumptions budget_correspondence.

(* Proposition E.1: the first line of A5 *)
Check @ledger_fidelity.
Print Assumptions ledger_fidelity.

(* Adequacy for the budget *)
Check @budget_adequacy.
Print Assumptions budget_adequacy.

(* The bound after closing (Eq. post-closing budget) *)
Check @budget_after_closing.
Print Assumptions budget_after_closing.

(* The booking correspondence *)
Check @bookingρ.

(* Proposition E.2 (Preserving booking correspondence) *)
Check @booking_correspondence.
Print Assumptions booking_correspondence.

(* From a recorded confirmation to a held reservation *)
Check @booking_goal.
Print Assumptions booking_goal.

(** ** Appendix F: what goes wrong without isolation *)

(* What goes wrong without isolation *)
Check @ungated_unsafe.
Print Assumptions ungated_unsafe.

(** ** Appendix G: isolation, stepwise *)

(* A7 as stated implies (NI1) and (NI2) *)
Check @System.A7_isolation.
Print Assumptions System.A7_isolation.

(* Lemma G.1 (Isolation, stepwise formulation) *)
Check @isolation_stepwise.
Print Assumptions isolation_stepwise.

(** ** The travel contract (Table 1) and Fig. 2 *)

(* Table 1: the travel contract, as a standard contract *)
Check @Travel.spec.
Check @Travel.B.
Check @Travel.Goal.

(* Outside changes, as a test, and what it says *)
Check @Travel.out.
Check @Travel.outP.
Print Assumptions Travel.outP.

(* The travel contract satisfies A3 *)
Check @Travel.cert.
Print Assumptions Travel.cert.

(* Episode 1: booking the unrated partner hotel is rejected *)
Check @Travel.ep1_book_rejected.
Print Assumptions Travel.ep1_book_rejected.

(* Episode 1: asking the expert is admissible *)
Check @Travel.ep1_rate.
Print Assumptions Travel.ep1_rate.

(* Episode 1: asking again returns the recorded rating *)
Check @Travel.ep1_rate_again.
Print Assumptions Travel.ep1_rate_again.

(* Episode 2: booking Aurora for 900 is admissible *)
Check @Travel.ep2_book.
Print Assumptions Travel.ep2_book.

(* Episode 3: downloading mail is admissible *)
Check @Travel.ep3_download.
Print Assumptions Travel.ep3_download.

(* Episode 3: the injected recipient is rejected *)
Check @Travel.ep3_injection_rejected.
Print Assumptions Travel.ep3_injection_rejected.

(* Episode 4: settling before the goal is rejected *)
Check @Travel.ep4_premature.
Print Assumptions Travel.ep4_premature.

(* Episode 4: settling once the goal holds is admissible *)
Check @Travel.ep4_settle.
Print Assumptions Travel.ep4_settle.

(** ** Rocq only: Algorithms 1–2 as programs (no Lean counterpart)

[PC2/Program.v] implements Algorithm 1, with Algorithm 2's progress as an input,
as the function [step], and its runs as [run], and proves that they implement
the relations [Next], [Run] and [Reach] above. *)

(* Algorithm 2's progress at an iteration, and what the verdict becomes *)
Check @CheckEv.
Check @complete.
Check @completeP.
Print Assumptions completeP.

(* Algorithm 1, one iteration, and its correctness *)
Check @step.
Check @step_sound.
Print Assumptions step_sound.
Check @step_complete.
Print Assumptions step_complete.
Check @nextP.
Print Assumptions nextP.

(* Runs *)
Check @run.
Check @run_sound.
Print Assumptions run_sound.
Check @run_complete.
Print Assumptions run_complete.
Check @reach_run.
Print Assumptions reach_run.

(* The call discipline and no veto, for the program *)
Check @step_call_discipline.
Print Assumptions step_call_discipline.
Check @step_no_veto.
Print Assumptions step_no_veto.
