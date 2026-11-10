(** * Capability modules (§6): Definitions 5–7, Propositions 2–4, Theorem 6

A capability module packages a world, a state, a correspondence, and tools whose
effects (for reference executions) are known, including an idle tool. Coverage
and fidelity are established module by module; Theorem 6 combines them for tools
that are tensors of module tools, given compatibility of effects.

Products are taken over any index type [ι] (a module per index, ['I_n] for [n]
modules), as dependent functions; regrouping and permuting the factors is
reindexing. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From PC2 Require Import Basic Airlock Execution.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

(** Effects of a tool with inputs [I], over worlds [W] and states [S]: [e i w s
w' s'] when an invocation on [i] from [(w, s)] can reach [(w', s')]. *)
Definition Eff (I W S : Type) : Type := I -> W -> S -> W -> S -> Prop.

Module CapModule.

(** **Definition 5 (Capability module).** A world, a state, a correspondence;
tools over the state with their effects, [eff l i w s w' s'] (an invocation of
the tool [l] on [i] from [(w, s)] can reach [(w', s')], for reference
executions); and the idle tool, which waits without intervening. *)
Record t := Build {
  W : Type;
  S : Type;
  ρ : W -> S -> Prop;
  Name : Type;
  tools : Name -> Tool S;
  eff : forall l : Name, Eff (Tool.Inp (tools l)) W S;
  idle : Name;
}.

Section CapModule.

Variable M : t.

(** Local coverage [Cov_M(T)] (Eq. local-cov). *)
Definition Cov (l : Name M) : Prop :=
  forall i s s', Tool.En (tools M l) i s ->
    (exists w w', eff M l i w s w' s') -> Tool.D (tools M l) i s s'.

(** Local fidelity [Fid_M(T)] (Eq. local-fid). *)
Definition Fid (l : Name M) : Prop :=
  forall i w s w' s', ρ M w s -> Tool.En (tools M l) i s ->
    eff M l i w s w' s' -> ρ M w' s'.

End CapModule.

Arguments Cov : clear implicits.
Arguments Fid : clear implicits.

End CapModule.

Abbreviation CapModule := CapModule.t.

Import CapModule.

(** ** Tensors, compatibility, and Theorem 6 *)

Section Tensor.

Variables (ι : Type) (M : ι -> CapModule).

(** The worlds and the states of the product. *)
Local Abbreviation Wp := (forall k, W (M k)).
Local Abbreviation Sp := (forall k, S (M k)).

(** The tensor of one tool from each module (Eq. product-model): inputs and
states componentwise, the conjunction of the models. *)
Definition tensor (sel : forall k, Name (M k)) : Tool Sp :=
  @Tool.Build Sp (forall k, Tool.Inp (tools (M k) (sel k)))
    (fun i s s' => forall k, Tool.D (tools (M k) (sel k)) (i k) (s k) (s' k)).

(** The correspondence of the product: componentwise. *)
Definition prodρ (w : Wp) (s : Sp) : Prop :=
  forall k, ρ (M k) (w k) (s k).

(** **Compatibility of effects** (Eq. no-coupling): each effect of the tensor,
as it runs in the combined system, projects to an effect of each component, idle
components included. *)
Definition Compatible (sel : forall k, Name (M k))
    (effT : Eff (Tool.Inp (tensor sel)) Wp Sp) : Prop :=
  forall i w s w' s', effT i w s w' s' ->
    forall k, eff (M k) (sel k) (i k) (w k) (s k) (w' k) (s' k).

Arguments tensor : clear implicits.
Arguments prodρ : clear implicits.
Arguments Compatible : clear implicits.

(** An enabled tensor has every component enabled. *)
Lemma tensor_en {sel : forall k, Name (M k)} {i : Tool.Inp (tensor sel)}
    {s : Sp} :
  Tool.En (tensor sel) i s ->
  forall k, Tool.En (tools (M k) (sel k)) (i k) (s k).
Proof. by move=> [s' hs'] k; exists (s' k). Qed.

(** **Theorem 6 (From local to global guarantees)**, coverage. *)
Theorem local_to_global_cov (sel : forall k, Name (M k))
    (effT : Eff (Tool.Inp (tensor sel)) Wp Sp) :
  Compatible sel effT -> (forall k, Cov (M k) (sel k)) ->
  forall i s s', Tool.En (tensor sel) i s -> (exists w w', effT i w s w' s') ->
    Tool.D (tensor sel) i s s'.
Proof.
move=> hcomp hcov i s s' hen [w [w' he]] k.
by apply: hcov;
  [exact: tensor_en hen k | exists (w k), (w' k); exact: hcomp he k].
Qed.

(** **Theorem 6 (From local to global guarantees)**, fidelity (the first line of
A5). *)
Theorem local_to_global_fid (sel : forall k, Name (M k))
    (effT : Eff (Tool.Inp (tensor sel)) Wp Sp) :
  Compatible sel effT -> (forall k, Fid (M k) (sel k)) ->
  forall i w s w' s', prodρ w s -> Tool.En (tensor sel) i s ->
    effT i w s w' s' -> prodρ w' s'.
Proof.
move=> hcomp hfid i w s w' s' hρ hen he k.
by apply: hfid (hρ k) (tensor_en hen k) _; exact: hcomp he k.
Qed.

End Tensor.

Arguments tensor {ι} M sel.
Arguments prodρ {ι} M w s.
Arguments Compatible {ι} M sel effT.
Arguments tensor_en {ι M sel i s} _ k.
Arguments local_to_global_cov {ι M} sel effT _ _ i s s' _ _.
Arguments local_to_global_fid {ι M} sel effT _ _ i w s w' s' _ _ _.

Module Composite.

(** **A contract built from modules** (§6.2, "Building a contract"): its tools
and its control step are tensors of module tools, with their effects in the
combined system; the contract supplies its clause, view and inactivity test. *)
Record t {ι : Type} (M : ι -> CapModule) := Build {
  Name : Type;
  sel : Name -> forall k, CapModule.Name (M k);
  effT : forall l : Name,
    Eff (Tool.Inp (tensor M (sel l))) (forall k, W (M k)) (forall k, S (M k));
  selCtrl : forall k, CapModule.Name (M k);
  ctrlInp : Tool.Inp (tensor M selCtrl);
  effCtrl : (forall k, W (M k)) -> (forall k, S (M k)) ->
    (forall k, W (M k)) -> (forall k, S (M k)) -> Prop;
}.

Section Composite.

Variables (ι : Type) (M : ι -> CapModule) (X : t M).

Local Abbreviation Wp := (forall k, W (M k)).
Local Abbreviation Sp := (forall k, S (M k)).

(** The contract, for a clause, a view and an inactivity test on the combined
state. *)
Definition contract (C : Sp -> Prop) (V : Type) (view : Sp -> V)
    (stop : Sp -> bool) : Contract Sp :=
  @Contract.Build Sp C V view (Name X) (fun l => tensor M (sel X l))
    (fun s s' => Tool.D (tensor M (selCtrl X)) (ctrlInp X) s s') stop.

(** Its effects in the combined system. *)
Definition effects (C : Sp -> Prop) (V : Type) (view : Sp -> V)
    (stop : Sp -> bool) : Effects (contract C view stop) Wp :=
  @Effects.Build _ (contract C view stop) _
    (fun c => effT X (projT1 c) (projT2 c)) (effCtrl X).

(** **Theorem 6 for a contract built from modules.** With compatible effects,
local coverage of every module tool gives A2, and local fidelity gives the first
line of A5, for the contract's tools and its control step. *)
Theorem local_to_global (C : Sp -> Prop) (V : Type) (view : Sp -> V)
    (stop : Sp -> bool) :
  (forall l, Compatible M (sel X l) (effT X l)) ->
  Compatible M (selCtrl X)
    (fun i w s w' s' => i = ctrlInp X /\ effCtrl X w s w' s') ->
  (forall k (l : CapModule.Name (M k)), Cov (M k) l) ->
  Coverage (contract C view stop) (effects C view stop).
Proof.
move=> hcomp hcompC hcov; split=> [[l i] s s' hen he|s s' hen [w [w' he]]].
  exact: (local_to_global_cov _ _ (hcomp l) (fun k => hcov k _) i s s' hen he).
apply: (local_to_global_cov _ _ hcompC (fun k => hcov k _) (ctrlInp X)
  s s' hen).
by exists w, w'.
Qed.

Theorem local_to_global_fidelity (C : Sp -> Prop) (V : Type) (view : Sp -> V)
    (stop : Sp -> bool) :
  (forall l, Compatible M (sel X l) (effT X l)) ->
  Compatible M (selCtrl X)
    (fun i w s w' s' => i = ctrlInp X /\ effCtrl X w s w' s') ->
  (forall k (l : CapModule.Name (M k)), Fid (M k) l) ->
  (forall (c : Contract.Call (contract C view stop)) w s w' s', prodρ M w s ->
    (exists s'', Contract.D (contract C view stop) c s s'') ->
    Effects.ecall (effects C view stop) c w s w' s' -> prodρ M w' s') /\
  (forall w s w' s', prodρ M w s ->
    (exists s'', Contract.ctrl (contract C view stop) s s'') ->
    Effects.ectrl (effects C view stop) w s w' s' -> prodρ M w' s').
Proof.
move=> hcomp hcompC hfid;
  split=> [[l i] w s w' s' hρ hen he|w s w' s' hρ hen he].
  exact: (local_to_global_fid _ _ (hcomp l) (fun k => hfid k _)
    i w s w' s' hρ hen he).
exact: (local_to_global_fid _ _ hcompC (fun k => hfid k _) (ctrlInp X)
  w s w' s' hρ hen).
Qed.

End Composite.

Arguments contract {ι M} X C {V} view stop.
Arguments effects {ι M} X C {V} view stop.
Arguments local_to_global {ι M} X C {V} view stop _ _ _.
Arguments local_to_global_fidelity {ι M} X C {V} view stop _ _ _.

End Composite.

(** ** Restriction and extension (§6.4) *)

(** A precondition keeps local coverage (§6.4): the restricted model is enabled
only where the original one is, and agrees with it there. *)
Lemma cov_restrict {S W : Type} (T : Tool S) (Pre : Tool.Inp T -> S -> Prop)
    (eff : Eff (Tool.Inp T) W S) :
  (forall i s s', Tool.En T i s -> (exists w w', eff i w s w' s') ->
    Tool.D T i s s') ->
  forall i s s', Tool.En (Tool.restrict T Pre) i s ->
    (exists w w', eff i w s w' s') -> Tool.D (Tool.restrict T Pre) i s s'.
Proof.
by move=> h i s s' /Tool.en_restrict[hp hen'] he; split=> //; exact: h.
Qed.

(** A precondition keeps local fidelity (§6.4). *)
Lemma fid_restrict {S W : Type} (T : Tool S) (Pre : Tool.Inp T -> S -> Prop)
    (eff : Eff (Tool.Inp T) W S) (ρ : W -> S -> Prop) :
  (forall i w s w' s', ρ w s -> Tool.En T i s -> eff i w s w' s' -> ρ w' s') ->
  forall i w s w' s', ρ w s -> Tool.En (Tool.restrict T Pre) i s ->
    eff i w s w' s' -> ρ w' s'.
Proof. by move=> h i w s w' s' hρ /Tool.en_restrict[_ hen]; exact: h. Qed.

(** **Definition 7 (Extension)**: new state [Z], a correspondence [ρ'] for it,
and new tools on the full state; the retained tools keep [z] unchanged (Eq.
extension-model). *)
Definition ext (M : CapModule) (Z : Type) (ρ' : W M -> S M -> Z -> Prop)
    (N : Type) (new : N -> Tool (S M * Z))
    (effNew : forall n : N, Eff (Tool.Inp (new n)) (W M) (S M * Z))
    (effOld : forall l : CapModule.Name M,
      Eff (Tool.Inp (tools M l)) (W M) (S M * Z)) : CapModule :=
  let tl (l : CapModule.Name M + N) : Tool (S M * Z) :=
    match l with
    | inl l => @Tool.Build _ (Tool.Inp (tools M l))
        (fun i sz sz' => Tool.D (tools M l) i sz.1 sz'.1 /\ sz'.2 = sz.2)
    | inr n => new n
    end in
  @CapModule.Build (W M) (S M * Z) (fun w sz => ρ M w sz.1 /\ ρ' w sz.1 sz.2)
    (CapModule.Name M + N) tl
    (fun l => match l return Tool.Inp (tl l) -> _ with
      | inl l => effOld l
      | inr n => effNew n
      end)
    (inl (idle M)).

Arguments ext : clear implicits.

(** **Checking an extension** (§6.4), for the retained tools: if their effects
in the extended system project within their original effects and leave [z]
unchanged, their coverage proofs establish the lifted models; if moreover they
preserve the added correspondence, their fidelity proofs give fidelity in the
extended module. *)
Lemma ext_retained (M : CapModule) (Z : Type) (ρ' : W M -> S M -> Z -> Prop)
    (N : Type) (new : N -> Tool (S M * Z))
    (effNew : forall n : N, Eff (Tool.Inp (new n)) (W M) (S M * Z))
    (effOld : forall l : CapModule.Name M,
      Eff (Tool.Inp (tools M l)) (W M) (S M * Z))
    (l : CapModule.Name M)
    (hproj : forall i w sz w' sz', effOld l i w sz w' sz' ->
      eff M l i w sz.1 w' sz'.1 /\ sz'.2 = sz.2) :
  (Cov M l -> Cov (ext M Z ρ' N new effNew effOld) (inl l)) /\
  (Fid M l ->
    (forall i w sz w' sz', ρ M w sz.1 -> ρ' w sz.1 sz.2 ->
      Tool.En (tools M l) i sz.1 -> effOld l i w sz w' sz' ->
      ρ' w' sz'.1 sz'.2) ->
    Fid (ext M Z ρ' N new effNew effOld) (inl l)).
Proof.
split=> [hcov i sz sz' [s'' hs''] [w [w' he]]|hfid hρ' i w sz w' sz' hρ
  [s'' hs''] he].
  have [he₁ hz] := hproj i w sz w' sz' he.
  by split=> //; apply: hcov; [exists s''.1; exact: hs''.1 | exists w, w'].
have [he₁ _] := hproj i w sz w' sz' he.
have hen : Tool.En (tools M l) i sz.1 by exists s''.1; exact: hs''.1.
by split; [exact: hfid hρ.1 hen he₁ | exact: hρ' hρ.1 hρ.2 hen he].
Qed.

(** ** Three capability constructions (§6.3) *)

Section Custody.

Variables (Instr Wc : Type) (J : Wc -> Instr -> Prop).

(** **The custody module** (Eq. custody-module): the register of payment
instructions, [issue j], and idle; every submitted instruction is registered. *)
Definition custody (effIssue : Eff Instr Wc (Instr -> Prop))
    (effIdle : Wc -> (Instr -> Prop) -> Wc -> (Instr -> Prop) -> Prop) :
  CapModule :=
  let tl (b : bool) : Tool (Instr -> Prop) :=
    if b then @Tool.Build _ Instr
      (fun j s s' => s' = s \/ s' = fun y => s y \/ y = j)
    else @Tool.Build _ unit (fun _ s s' => s' = s) in
  @CapModule.Build Wc (Instr -> Prop) (fun w s => forall j, J w j -> s j)
    bool tl (fun b => if b return Tool.Inp (tl b) -> _ then effIssue
      else fun _ => effIdle) false.

(** **Proposition 2 (Custody).** Under (H1) only [issue j] changes the register,
by adding [j], and idle leaves it unchanged; and (H2) an instruction is
submitted only by [issue], once it is registered: both tools, idle included, are
covered and faithful. *)
Theorem custody_guarantees (effIssue : Eff Instr Wc (Instr -> Prop))
    (effIdle : Wc -> (Instr -> Prop) -> Wc -> (Instr -> Prop) -> Prop)
    (H1 : (forall j w s w' s', effIssue j w s w' s' ->
        s' = s \/ s' = fun y => s y \/ y = j) /\
      (forall w s w' s', effIdle w s w' s' -> s' = s))
    (H2 : (forall j w s w' s', effIssue j w s w' s' -> forall y, J w' y ->
        J w y \/ (y = j /\ s' y)) /\
      (forall w s w' s', effIdle w s w' s' -> forall y, J w' y -> J w y)) :
  forall l,
    Cov (custody effIssue effIdle) l /\ Fid (custody effIssue effIdle) l.
Proof.
case; rewrite /Cov /Fid /=; split.
- by move=> j s s' _ [w [w' he]]; exact: H1.1 he.
- move=> j w s w' s' hρ _ he y hy.
  have hgrow : forall y, s y -> s' y
    by case: (H1.1 _ _ _ _ _ he) => -> // y' h; left.
  by case: (H2.1 _ _ _ _ _ he y hy) => [/hρ /hgrow|[_]].
- by move=> _ s s' _ [w [w' he]]; exact: H1.2 he.
- move=> _ w s w' s' hρ _ he y hy.
  by rewrite (H1.2 _ _ _ _ he); exact/hρ/(H2.2 _ _ _ _ he).
Qed.

End Custody.

Arguments custody {Instr Wc} J effIssue effIdle.
Arguments custody_guarantees {Instr Wc} J effIssue effIdle H1 H2 l.

Section Interface.

Variables (Req Resp Wf : Type) (request : Resp -> Req) (Spec : Resp -> Prop)
  (H : Wf -> Resp -> Prop).

(** **The formal-interface module** (Eq. interface-module): a log of response
events, [query q], and idle; every recorded response was issued by the service
and is permitted by its specification. *)
Definition interface (effQuery : Eff Req Wf (Resp -> Prop))
    (effIdle : Wf -> (Resp -> Prop) -> Wf -> (Resp -> Prop) -> Prop) :
  CapModule :=
  let tl (b : bool) : Tool (Resp -> Prop) :=
    if b then @Tool.Build _ Req
      (fun q s s' => s' = s \/
        exists e, request e = q /\ Spec e /\ s' = fun y => s y \/ y = e)
    else @Tool.Build _ unit (fun _ s s' => s' = s) in
  @CapModule.Build Wf (Resp -> Prop)
    (fun w s => forall e, s e -> H w e /\ Spec e) bool tl
    (fun b => if b return Tool.Inp (tl b) -> _ then effQuery
      else fun _ => effIdle) false.

(** **Proposition 3 (Formal interface).** If the history retains its events,
(F1) every response issued by the service satisfies the specification, and (F2)
only [query q] changes the log, leaving it unchanged or appending one event
issued for [q], while idle leaves it unchanged: both tools, idle included, are
covered and faithful. *)
Theorem interface_guarantees (effQuery : Eff Req Wf (Resp -> Prop))
    (effIdle : Wf -> (Resp -> Prop) -> Wf -> (Resp -> Prop) -> Prop)
    (retain : (forall q w s w' s', effQuery q w s w' s' ->
        forall e, H w e -> H w' e) /\
      (forall w s w' s', effIdle w s w' s' -> forall e, H w e -> H w' e))
    (F1 : forall w e, H w e -> Spec e)
    (F2 : (forall q w s w' s', effQuery q w s w' s' ->
        s' = s \/
        exists e, request e = q /\ H w' e /\ s' = fun y => s y \/ y = e) /\
      (forall w s w' s', effIdle w s w' s' -> s' = s)) :
  forall l,
    Cov (interface effQuery effIdle) l /\ Fid (interface effQuery effIdle) l.
Proof.
case; rewrite /Cov /Fid /=; split.
- move=> q s s' _ [w [w' he]].
  case: (F2.1 _ _ _ _ _ he) => [->|[e [hq [hH ->]]]]; first by left.
  by right; exists e; do !split=> //; exact: F1 hH.
- move=> q w s w' s' hρ _ he e.
  have old : s e -> H w' e /\ Spec e
    by move=> /hρ[hH hS]; split=> //; exact: retain.1 he e hH.
  case: (F2.1 _ _ _ _ _ he) => [->|[e' [_ [hH ->]]]] //.
  by case=> [/old //|->]; split=> //; exact: F1 hH.
- by move=> _ s s' _ [w [w' he]]; exact: F2.2 he.
- move=> _ w s w' s' hρ _ he e; rewrite (F2.2 _ _ _ _ he) => hs'.
  by have [hH hS] := hρ e hs'; split=> //; exact: retain.2 he e hH.
Qed.

End Interface.

Arguments interface {Req Resp Wf} request Spec H effQuery effIdle.
Arguments interface_guarantees {Req Resp Wf} request Spec H effQuery effIdle
  retain F1 F2 l.

Section Invariant.

(** **Proposition 4 (Domain invariant).** For a module whose correspondence is
[s = π(w) ∧ K(w)] (Eq. shared-model-transition): if (M1) the state at every
instant is [π] of the world, and (M2) every enabled tool, idle included,
preserves [K], then every tool is faithful; and adequacy follows from [K(w) ∧
C(π(w)) → Safe(w)] (Eq. shared-model-adequacy). *)
Theorem domain_invariant (M : CapModule) (π : W M -> S M) (Kinv : W M -> Prop)
    (hρ : forall w s, ρ M w s <-> s = π w /\ Kinv w)
    (M1 : forall l i w s w' s', eff M l i w s w' s' -> s' = π w')
    (M2 : forall l i w s w' s', Tool.En (tools M l) i s -> Kinv w ->
      eff M l i w s w' s' -> Kinv w') :
  (forall l, Fid M l) /\
  forall (C : S M -> Prop) (Safe : W M -> Prop),
    (forall w, Kinv w -> C (π w) -> Safe w) ->
    forall w s, ρ M w s -> C s -> Safe w.
Proof.
split=> [l i w s w' s' /hρ[_ hK] hen he|C Safe hadq w s /hρ[-> hK] hc].
  by apply/hρ; split; [exact: M1 he | exact: M2 hen hK he].
exact: hadq.
Qed.

End Invariant.
