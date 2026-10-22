import PC2.Basic

/-!
# The Airlock (§3.4): Algorithms 1 and 2

Algorithm 1 and the proof-checking routine of Algorithm 2 (App. B), as a transition system at the level
of operations. A configuration holds Algorithm 1's variables, Algorithm 2's shared verdict and where
the loop is. From a configuration, the steps of the loop that perform no operation (publishing the
view, receiving a request, a running check finishing or not) lead to one operation, a tool call or a
control step; when it returns, its reading becomes the record.

The agent's requests are inputs, and when a running check finishes is left open: the runs cover every
sequence of requests and proofs, and every interleaving of the parallel checker with the loop.

Two facts need nothing but the algorithm: every call it makes satisfies the call discipline of
A4 (iii) (`call_discipline`), and nobody can veto a call whose proof was accepted (`no_veto`).
-/

namespace PC2

variable {S : Type}

/-- A request `(T, i, k₀, n, π)`: the call (a tool of the contract and an input of it, so that `T ∈ 𝒯`
and `i ∈ I_T` hold by typing), the index of the view its proof is based on, the allowance, the
proof. -/
structure Request (K : Contract S) (P : Type) where
  call : K.Call
  k₀ : Nat
  n : Nat
  π : P

/-- What the agent's channel gives the loop at line 6: nothing (`tool_call_ready()` is false), a request
that is not of the contract's form (a tool not in `𝒯`, or an input not in `I_T`), or a request. -/
inductive Input (K : Contract S) (P : Type) where
  | none
  | malformed
  | request (q : Request K P)

/-- The checker, abstractly: which proofs it accepts for which statements. -/
structure Checker (P : Type) where
  accepts : P → Prop → Prop

/-- **A1 (Sound checking).** If the checker accepts `π` as a proof of `Φ`, then `Φ` holds. -/
def Checker.Sound {P : Type} (ch : Checker P) : Prop :=
  ∀ (π : P) (Φ : Prop), ch.accepts π Φ → Φ

/-- An operation of the Airlock: a control step, or the call of a request. -/
inductive Op (K : Contract S) (P : Type) where
  | ctrl
  | call (q : Request K P)

/-- The model of an operation. -/
def Op.model {K : Contract S} {P : Type} : Op K P → S → S → Prop
  | .ctrl => K.ctrl
  | .call q => K.D q.call

/-- Algorithm 2's shared verdict `r`. A running check keeps the arguments it was started with: the
iteration of the last call, and the index of the last published view. -/
inductive Verdict where
  | none
  | computing (kLast : Int) (k : Nat)
  | correct
  | incorrect

/-- Where the loop is: before initialization, at the start of an iteration, or after a call. -/
inductive Phase where
  | init
  | top
  | afterCall
  deriving DecidableEq

/-- Algorithm 1's variables: the record (the last reading), the published views `v`, the number `k`
of control steps of the loop, the iteration `kLast` of the last call, the current request; Algorithm
2's verdict; and where the loop is. -/
structure Vars (K : Contract S) (P : Type) where
  record : S
  v : List K.V
  k : Nat
  kLast : Int
  req : Option (Request K P)
  r : Verdict
  phase : Phase

section Algorithm

variable (K : Contract S) {P : Type} (ch : Checker P) (πK : P)

/-- The variables when the Airlock starts (Algorithm 1, line 1, and Algorithm 2's `r ← none`), with the
record `s₀`, the reading taken when the Airlock starts. -/
def start (s₀ : S) : Vars K P := ⟨s₀, [], 0, -1, none, .none, .init⟩

/-- **Algorithm 2, `check`**: what a check computes from its arguments, the iteration `kLast` of the
last call and the index `k` of the last published view. The views `v` it reads have only grown since
it started. -/
def checkOK (q : Request K P) (kLast : Int) (k : Nat) (v : List K.V) : Prop :=
  kLast < q.k₀ ∧ q.k₀ ≤ k ∧ k ≤ q.k₀ + q.n ∧
    ∃ v₀, v[q.k₀]? = some v₀ ∧ ch.accepts q.π (K.OblN q.n q.call v₀)

/-- Line 5: `v[k] ← read_view(); publish_view(k, v[k])`. -/
def publish (x : Vars K P) : Vars K P := { x with v := x.v ++ [K.view x.record] }

/-- Lines 6–8: if a request arrived, `start_proof_check` replaces the current one, and starts its check
with the current `k_last` and the views published so far, of which the check reads the index of the
last (Algorithm 2). A request not of the contract's form is replaced too, and its check fails at
`T ∈ 𝒯` or at `type_check`; nothing else depends on it. -/
def receive (inp : Input K P) (x : Vars K P) : Vars K P :=
  match inp with
  | .none => x
  | .malformed => { x with req := none, r := .incorrect }
  | .request q => { x with req := some q, r := .computing x.kLast (x.v.length - 1) }

/-- Algorithm 2: a running check may finish. It accepts only if what `check` computes holds; it may
reject at any time, as a real checker may also fail or give up. -/
inductive Complete : Vars K P → Vars K P → Prop
  | wait (x : Vars K P) : Complete x x
  | accept (x : Vars K P) (q : Request K P) (kl : Int) (k : Nat) :
      x.req = some q → x.r = .computing kl k → checkOK K ch q kl k x.v →
      Complete x { x with r := .correct }
  | reject (x : Vars K P) (q : Request K P) (kl : Int) (k : Nat) :
      x.req = some q → x.r = .computing kl k → Complete x { x with r := .incorrect }

/-- **Algorithm 1**, at the level of operations. From `x`, with the agent's input `inp`, the Airlock
invokes `op`; once `op` returns with the reading `s`, the variables are `κ s`.
- `init` (lines 2–3): the certificate `π_𝒦` is accepted as a proof of A3 and the state is inactive;
  control initializes.
- `call` (lines 4–10): the contract is active; the view is published (5), a request may arrive and its
  check start (6–8), a running check may finish; the current request's proof is correct and
  `k ≤ k₀ + n` (9): its call runs, then `k_last ← k` and the proof is consumed (10).
- `ctrl` (lines 4–9, 11–12): the same, with no call authorized at line 9; control runs, and
  `k ← k + 1`.
- `ctrlAfterCall` (lines 11–12): after a call, if the contract is still active, control runs, and
  `k ← k + 1`; the loop then returns to line 4. -/
inductive Next : Vars K P → Input K P → Op K P → (S → Vars K P) → Prop
  | init (x : Vars K P) (inp : Input K P) :
      x.phase = .init → ch.accepts πK K.Cert → ¬ K.Active x.record →
      Next x inp .ctrl (fun s => { x with record := s, phase := .top })
  | call (x x₂ : Vars K P) (inp : Input K P) (q : Request K P) :
      x.phase = .top → K.Active x.record → Complete K ch (receive K inp (publish K x)) x₂ →
      x₂.req = some q → x₂.r = .correct → x₂.k ≤ q.k₀ + q.n →
      Next x inp (.call q)
        (fun s => { x₂ with record := s, kLast := x₂.k, r := .none, phase := .afterCall })
  | ctrl (x x₂ : Vars K P) (inp : Input K P) :
      x.phase = .top → K.Active x.record → Complete K ch (receive K inp (publish K x)) x₂ →
      ¬ (x₂.r = .correct ∧ ∃ q, x₂.req = some q ∧ x₂.k ≤ q.k₀ + q.n) →
      Next x inp .ctrl (fun s => { x₂ with record := s, k := x₂.k + 1 })
  | ctrlAfterCall (x : Vars K P) (inp : Input K P) :
      x.phase = .afterCall → K.Active x.record →
      Next x inp .ctrl (fun s => { x with record := s, k := x.k + 1, phase := .top })

/-- The configurations Algorithm 1 reaches from the reading `s₀`, for any inputs and readings. -/
inductive Reach (s₀ : S) : Vars K P → Prop
  | start : Reach s₀ (start K s₀)
  | step {x : Vars K P} {inp : Input K P} {op : Op K P} {κ : S → Vars K P} (s : S) :
      Reach s₀ x → Next K ch πK x inp op κ → Reach s₀ (κ s)

/-- The runs of Algorithm 1 from the reading `s₀`, with their trace: each operation, with the input of
the iteration that chose it and the reading at its end. -/
inductive Run (s₀ : S) : Vars K P → List (Input K P × Op K P × S) → Prop
  | start : Run s₀ (start K s₀) []
  | step {x : Vars K P} {inp : Input K P} {op : Op K P} {κ : S → Vars K P}
      {tr : List (Input K P × Op K P × S)} (s : S) :
      Run s₀ x tr → Next K ch πK x inp op κ → Run s₀ (κ s) (tr ++ [(inp, op, s)])

/-! ## The invariant of the algorithm -/

/-- Algorithm 2's verdict agrees with the variables: a running check was started for the current
request with the current `k_last`; an accepted verdict means that the current request's check passed. -/
structure Chk (x : Vars K P) : Prop where
  computing : ∀ kl k, x.r = .computing kl k → ∃ q, x.req = some q ∧ kl = x.kLast ∧ k ≤ x.k
  correct : x.r = .correct → ∃ q v₀, x.req = some q ∧ x.kLast < q.k₀ ∧ q.k₀ ≤ x.k ∧
    x.v[q.k₀]? = some v₀ ∧ ch.accepts q.π (K.OblN q.n q.call v₀)

/-- The invariant of Algorithm 1 between operations. -/
structure Wf (x : Vars K P) : Prop where
  init : x.phase = .init → x.v = [] ∧ x.k = 0 ∧ x.r = .none
  top : x.phase = .top → x.v.length = x.k
  after : x.phase = .afterCall → x.v.length = x.k + 1 ∧ x.kLast = x.k ∧ x.r = .none
  chk : Chk K ch x

variable {K} {ch} {πK}

theorem publish_fields (x : Vars K P) :
    (publish K x).record = x.record ∧ (publish K x).v = x.v ++ [K.view x.record] ∧
    (publish K x).k = x.k ∧ (publish K x).kLast = x.kLast ∧ (publish K x).req = x.req ∧
    (publish K x).r = x.r ∧ (publish K x).phase = x.phase :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem receive_fields (inp : Input K P) (x : Vars K P) :
    (receive K inp x).record = x.record ∧ (receive K inp x).v = x.v ∧ (receive K inp x).k = x.k ∧
    (receive K inp x).kLast = x.kLast ∧ (receive K inp x).phase = x.phase := by
  cases inp <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem complete_fields {x x₂ : Vars K P} (h : Complete K ch x x₂) :
    x₂.record = x.record ∧ x₂.v = x.v ∧ x₂.k = x.k ∧ x₂.kLast = x.kLast ∧ x₂.phase = x.phase ∧
    x₂.req = x.req := by
  cases h <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem getElem?_append_of {α : Type} {l : List α} {a : α} {j : Nat} {b : α}
    (h : l[j]? = some b) : (l ++ [a])[j]? = some b := by
  have hj : j < l.length := (List.getElem?_eq_some_iff.1 h).1
  rw [List.getElem?_append_left hj]; exact h

theorem chk_publish {x : Vars K P} (h : Chk K ch x) : Chk K ch (publish K x) where
  computing kl k hr := h.computing kl k hr
  correct hr := by
    obtain ⟨q, v₀, hq, hlast, hk, hv, hacc⟩ := h.correct hr
    exact ⟨q, v₀, hq, hlast, hk, getElem?_append_of hv, hacc⟩

/-- Receiving a request after publishing, at the start of an iteration. -/
theorem chk_receive {x : Vars K P} (hW : Wf K ch x) (hx : x.phase = .top)
    (inp : Input K P) : Chk K ch (receive K inp (publish K x)) := by
  cases inp with
  | none => exact chk_publish hW.chk
  | malformed => exact ⟨fun _ _ h => by simp [receive] at h, fun h => by simp [receive] at h⟩
  | request q =>
    refine ⟨?_, ?_⟩
    · intro kl k hr
      simp only [receive, Verdict.computing.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨q, rfl, rfl, ?_⟩
      show (x.v ++ [K.view x.record]).length - 1 ≤ x.k
      simp [hW.top hx]
    · intro hr; simp [receive] at hr

theorem chk_complete {x x₂ : Vars K P} (hC : Chk K ch x) (h : Complete K ch x x₂) :
    Chk K ch x₂ := by
  match h with
  | .wait _ => exact hC
  | .accept _ q kl k hq hr hok =>
    refine ⟨fun _ _ h => by simp at h, fun _ => ?_⟩
    obtain ⟨q', hq', rfl, hk⟩ := hC.computing kl k hr
    obtain ⟨hlast, hk₀, _, v₀, hv, hacc⟩ := hok
    obtain rfl : q' = q := Option.some.inj (hq'.symm.trans hq)
    exact ⟨q', v₀, hq, hlast, Nat.le_trans hk₀ hk, hv, hacc⟩
  | .reject _ _ _ _ _ _ =>
    exact ⟨fun _ _ h => by simp at h, fun h => by simp at h⟩

/-- The verdict seen at the call-selection step of an iteration. -/
theorem chk_step {x x₂ : Vars K P} (hW : Wf K ch x) (hx : x.phase = .top)
    {inp : Input K P} (h : Complete K ch (receive K inp (publish K x)) x₂) :
    Chk K ch x₂ :=
  chk_complete (chk_receive hW hx inp) h

theorem wf_start (s₀ : S) : Wf K ch (start K s₀ : Vars K P) where
  init _ := ⟨rfl, rfl, rfl⟩
  top h := by simp [start] at h
  after h := by simp [start] at h
  chk := ⟨fun _ _ h => by simp [start] at h, fun h => by simp [start] at h⟩

/-- Algorithm 1 keeps its invariant. -/
theorem wf_next {x : Vars K P} {inp : Input K P} {op : Op K P} {κ : S → Vars K P}
    (hW : Wf K ch x) (h : Next K ch πK x inp op κ) (s : S) : Wf K ch (κ s) := by
  match h with
  | .init _ _ hx _ _ =>
    obtain ⟨hv, hk, hr⟩ := hW.init hx
    refine ⟨fun h => by simp at h, fun _ => by simp [hv, hk], fun h => by simp at h, ?_⟩
    exact ⟨fun _ _ h => by simp [hr] at h, fun h => by simp [hr] at h⟩
  | .call _ x₂ _ q hx _ hc _ _ _ =>
    obtain ⟨_, hv, hk, _, _, _⟩ := complete_fields hc
    obtain ⟨_, hv', hk', _, _⟩ := receive_fields inp (publish K x)
    refine ⟨fun h => by simp at h, fun h => by simp at h, fun _ => ⟨?_, rfl, rfl⟩, ?_⟩
    · show x₂.v.length = x₂.k + 1
      rw [hv, hv', hk, hk']; simp [publish, hW.top hx]
    · exact ⟨fun _ _ h => by simp at h, fun h => by simp at h⟩
  | .ctrl _ x₂ _ hx _ hc _ =>
    have hC := chk_step hW hx hc
    obtain ⟨_, hv, hk, _, hph, _⟩ := complete_fields hc
    obtain ⟨_, hv', hk', _, hph'⟩ := receive_fields inp (publish K x)
    refine ⟨fun h => ?_, fun _ => ?_, fun h => ?_, ?_⟩
    · simp only at h; rw [hph, hph'] at h; simp [publish, hx] at h
    · show x₂.v.length = x₂.k + 1
      rw [hv, hv', hk, hk']; simp [publish, hW.top hx]
    · simp only at h; rw [hph, hph'] at h; simp [publish, hx] at h
    · refine ⟨fun kl k hr => ?_, fun hr => ?_⟩
      · obtain ⟨q, hq, hkl, hk⟩ := hC.computing kl k hr
        exact ⟨q, hq, hkl, Nat.le_succ_of_le hk⟩
      · obtain ⟨q, v₀, hq, hlast, hk, hv, hacc⟩ := hC.correct hr
        exact ⟨q, v₀, hq, hlast, Nat.le_succ_of_le hk, hv, hacc⟩
  | .ctrlAfterCall _ _ hx _ =>
    obtain ⟨hlen, _, hr⟩ := hW.after hx
    refine ⟨fun h => by simp at h, fun _ => by simpa using hlen, fun h => by simp at h, ?_⟩
    exact ⟨fun _ _ h => by simp [hr] at h, fun h => by simp [hr] at h⟩

theorem Reach.wf {s₀ : S} {x : Vars K P} (h : Reach K ch πK s₀ x) : Wf K ch x := by
  induction h with
  | start => exact wf_start s₀
  | step s _ hn ih => exact wf_next ih hn s

theorem Run.reach {s₀ : S} {x : Vars K P} {tr : List (Input K P × Op K P × S)}
    (h : Run K ch πK s₀ x tr) : Reach K ch πK s₀ x := by
  induction h with
  | start => exact .start
  | step s _ hn ih => exact .step s ih hn

/-! ## A4 (iii), and no veto -/

/-- **The call discipline of A4 (iii) follows from Algorithms 1 and 2.** A call runs only from an
active state at the start of an iteration `k`, for the current request `(T, i, k₀, n, π)`, if no other
call ran since `v[k₀]` was published (`kLast < k₀`), with `k₀ ≤ k ≤ k₀ + n`, after the checker accepted
`π` as a proof of `Obl^{≤n}_T(i, v[k₀])`, a statement the Airlock forms itself from the published view
`v[k₀]`. -/
theorem call_discipline {s₀ : S} {x : Vars K P} {inp : Input K P} {q : Request K P}
    {κ : S → Vars K P} (hR : Reach K ch πK s₀ x) (h : Next K ch πK x inp (.call q) κ) :
    x.phase = .top ∧ K.Active x.record ∧ x.kLast < q.k₀ ∧ q.k₀ ≤ x.k ∧ x.k ≤ q.k₀ + q.n ∧
      ∃ v₀, (publish K x).v[q.k₀]? = some v₀ ∧ ch.accepts q.π (K.OblN q.n q.call v₀) := by
  match h with
  | .call _ x₂ _ _ hx ha hc hq hr hk =>
    have hC := chk_step hR.wf hx hc
    obtain ⟨q', v₀, hq', hlast, hk₀, hv, hacc⟩ := hC.correct hr
    obtain rfl : q' = q := Option.some.inj (hq'.symm.trans hq)
    obtain ⟨_, hv₂, hk₂, hl₂, _, _⟩ := complete_fields hc
    obtain ⟨_, hv', hk', hl', _⟩ := receive_fields inp (publish K x)
    rw [hl₂, hl'] at hlast; rw [hk₂, hk'] at hk₀ hk; rw [hv₂, hv'] at hv
    exact ⟨hx, ha, hlast, hk₀, hk, v₀, hv, hacc⟩

/-- **No veto (§4.2).** If the current request's proof has been accepted and its window is still valid,
and the agent sends no new request, the next operation is that call: nothing else can intervene. -/
theorem no_veto {x : Vars K P} {q : Request K P} {op : Op K P} {κ : S → Vars K P}
    (hx : x.phase = .top) (hr : x.r = .correct) (hq : x.req = some q) (hk : x.k ≤ q.k₀ + q.n)
    (h : Next K ch πK x .none op κ) : op = .call q := by
  match h with
  | .init _ _ h' _ _ => rw [hx] at h'; cases h'
  | .call _ x₂ _ q' _ _ hc hq' _ _ =>
    match hc with
    | .wait _ => simp only [receive, publish] at hq'; rw [hq] at hq'; cases hq'; rfl
    | .accept _ _ _ _ _ hr' _ => simp only [receive, publish] at hr'; rw [hr] at hr'; cases hr'
    | .reject _ _ _ _ _ hr' => simp only [receive, publish] at hr'; rw [hr] at hr'; cases hr'
  | .ctrl _ x₂ _ _ _ hc hno =>
    match hc with
    | .wait _ => exact absurd ⟨hr, q, hq, hk⟩ hno
    | .accept _ _ _ _ _ hr' _ => simp only [receive, publish] at hr'; rw [hr] at hr'; cases hr'
    | .reject _ _ _ _ _ hr' => simp only [receive, publish] at hr'; rw [hr] at hr'; cases hr'
  | .ctrlAfterCall _ _ h' _ => rw [hx] at h'; cases h'

end Algorithm

end PC2
