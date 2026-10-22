import PC2.Execution

/-!
# Anytime compliance (§4.1): Lemma 1 and Theorem 1

The proof follows the paper's. Between operations, the variables satisfy an invariant: once the
contract has started, the certificate holds (it was checked at startup, A1), the record complies, and
each view published since the last call was computed from a compliant active state whose window
reaches the record. A control step is then admissible by A3; a call, by its accepted obligation (A1)
applied through the Window lemma; and by A2 every instant of an operation is in its model.
-/

namespace PC2

variable {S : Type}

section

variable {K : Contract S} {P W : Type} {ch : Checker P} {πK : P} {E : Effects K W}

variable (K ch) in
/-- The invariant between operations. -/
structure Inv (x : Vars K P) : Prop where
  wf : Wf K ch x
  cert : x.phase ≠ .init → K.Cert
  comp : x.phase ≠ .init → K.Active x.record → K.C x.record
  views : x.phase = .top → K.Active x.record → ∀ (j : Nat) (v₀ : K.V), x.kLast < j →
    x.v[j]? = some v₀ → ∃ r, K.view r = v₀ ∧ K.Active r ∧ K.C r ∧ K.Win (x.k - j) r x.record

theorem inv_start (s₀ : S) : Inv K ch (start K s₀ : Vars K P) where
  wf := wf_start s₀
  cert h := absurd rfl h
  comp h := absurd rfl h
  views h := by simp [start] at h

/-- The facts behind a call, from Algorithm 1's invariant (A4 (iii)). -/
theorem call_facts {x : Vars K P} {inp : Input K P} {q : Request K P}
    {κ : S → Vars K P} (hW : Wf K ch x) (h : Next K ch πK x inp (.call q) κ) :
    x.phase = .top ∧ K.Active x.record ∧ x.kLast < q.k₀ ∧ q.k₀ ≤ x.k ∧ x.k ≤ q.k₀ + q.n ∧
      ∃ v₀, (publish K x).v[q.k₀]? = some v₀ ∧ ch.accepts q.π (K.OblN q.n q.call v₀) := by
  match h with
  | .call _ x₂ _ _ hx ha hc hq hr hk =>
    have hC := chk_step hW hx hc
    obtain ⟨q', v₀, hq', hlast, hk₀, hv, hacc⟩ := hC.correct hr
    obtain rfl : q' = q := Option.some.inj (hq'.symm.trans hq)
    obtain ⟨_, hv₂, hk₂, hl₂, _, _⟩ := complete_fields hc
    obtain ⟨_, hv', hk', hl', _⟩ := receive_fields inp (publish K x)
    rw [hl₂, hl'] at hlast; rw [hk₂, hk'] at hk₀ hk; rw [hv₂, hv'] at hv
    exact ⟨hx, ha, hlast, hk₀, hk, v₀, hv, hacc⟩

/-- **Lemma 1 (Window).** Let a call run for the request `(T, i, k₀, n, π)` from the record, at the
start of an iteration `k`, with no call since the view `v₀ = v[k₀]` was published (`kLast < k₀`) and
`k ≤ k₀ + n`. If the clause has held so far (the invariant), then the state `sv` from which `v₀` was
computed and the record are active, `sv` complies, and the record is in the window of `sv`:
`D^{≤n}_ctrl(sv, record)`. -/
theorem window {x : Vars K P} {q : Request K P} {v₀ : K.V} (hI : Inv K ch x)
    (hx : x.phase = .top) (ha : K.Active x.record) (hlast : x.kLast < q.k₀)
    (hk : x.k ≤ q.k₀ + q.n) (hv : (publish K x).v[q.k₀]? = some v₀) :
    ∃ sv, K.view sv = v₀ ∧ K.Active sv ∧ K.C sv ∧ K.Win q.n sv x.record := by
  have hlen := hI.wf.top hx
  have hc := hI.comp (by rw [hx]; simp) ha
  change (x.v ++ [K.view x.record])[q.k₀]? = some v₀ at hv
  by_cases hlt : q.k₀ < x.v.length
  · rw [List.getElem?_append_left hlt] at hv
    obtain ⟨r, hr, hra, hrc, hw⟩ := hI.views hx ha q.k₀ v₀ hlast hv
    exact ⟨r, hr, hra, hrc, K.win_mono (by omega) hw⟩
  · have hle : q.k₀ < x.v.length + 1 := by
      have := (List.getElem?_eq_some_iff.1 hv).1; simpa using this
    have heq : q.k₀ = x.v.length := by omega
    rw [heq, List.getElem?_append_right (Nat.le_refl _)] at hv
    simp at hv
    exact ⟨x.record, hv, ha, hc, K.win_mono (Nat.zero_le _) rfl⟩

/-- Under A1, an operation that Algorithm 1 invokes is enabled where it starts, and every state its
model admits complies; during initialization, every active one. -/
theorem next_safe (hA1 : ch.Sound) {x : Vars K P} {inp : Input K P} {o : Op K P}
    {κ : S → Vars K P} (hI : Inv K ch x) (h : Next K ch πK x inp o κ) :
    (∃ s', o.model x.record s') ∧
      ∀ s', o.model x.record s' → (x.phase ≠ .init ∨ K.Active s') → K.C s' := by
  match h with
  | .init _ _ hx hacc hin =>
    have hK : K.Cert := hA1 _ _ hacc
    refine ⟨hK.enabled _ hin, fun s' hs hor => ?_⟩
    rcases hor with hne | ha'
    · exact absurd hx hne
    · exact hK.initializer _ _ hin ha' hs
  | .call _ x₂ _ q hx₀ ha₀ hc hq hr hk₀ =>
    obtain ⟨hx, ha, hlast, _, hk, v₀, hv, hacc⟩ :=
      call_facts hI.wf (Next.call (πK := πK) x x₂ inp q hx₀ ha₀ hc hq hr hk₀)
    obtain ⟨sv, hvs, has, hcs, hw⟩ := window hI hx ha hlast hk hv
    have hadm := hA1 _ _ hacc sv x.record has ha hvs hcs hw
    exact ⟨hadm.1, fun s' hs _ => hadm.2 s' hs⟩
  | .ctrl _ _ _ hx ha _ _ =>
    have hne : x.phase ≠ .init := by rw [hx]; simp
    have hadm := (hI.cert hne).controller _ ha (hI.comp hne ha)
    exact ⟨hadm.1, fun s' hs _ => hadm.2 s' hs⟩
  | .ctrlAfterCall _ _ hx ha =>
    have hne : x.phase ≠ .init := by rw [hx]; simp
    have hadm := (hI.cert hne).controller _ ha (hI.comp hne ha)
    exact ⟨hadm.1, fun s' hs _ => hadm.2 s' hs⟩

/-- After an operation, the phase is never `init`. -/
theorem next_phase {x : Vars K P} {inp : Input K P} {o : Op K P} {κ : S → Vars K P}
    (h : Next K ch πK x inp o κ) (s : S) : (κ s).phase ≠ .init := by
  match h with
  | .init .. => simp
  | .call .. => simp
  | .ctrl _ x₂ _ hx _ hc _ =>
    obtain ⟨_, _, _, _, hph, _⟩ := complete_fields hc
    obtain ⟨_, _, _, _, hph'⟩ := receive_fields inp (publish K x)
    show x₂.phase ≠ .init
    rw [hph, hph']; simp [publish, hx]
  | .ctrlAfterCall .. => simp

/-- Under A1, the invariant holds after an operation whose reading its model admits. -/
theorem next_inv (hA1 : ch.Sound) {x : Vars K P} {inp : Input K P} {o : Op K P}
    {κ : S → Vars K P} (hI : Inv K ch x) (h : Next K ch πK x inp o κ) {s : S}
    (hs : o.model x.record s) : Inv K ch (κ s) := by
  have hsafe := next_safe hA1 hI h
  have hph := next_phase h s
  have hwf := wf_next hI.wf h s
  refine ⟨hwf, ?_, ?_, ?_⟩
  · -- the certificate
    intro _
    match h with
    | .init _ _ _ hacc _ => exact hA1 _ _ hacc
    | .call _ _ _ _ hx _ _ _ _ _ => exact hI.cert (by rw [hx]; simp)
    | .ctrl _ _ _ hx _ _ _ => exact hI.cert (by rw [hx]; simp)
    | .ctrlAfterCall _ _ hx _ => exact hI.cert (by rw [hx]; simp)
  · -- the record complies
    intro _ ha'
    match h with
    | .init .. => exact hsafe.2 s hs (Or.inr ha')
    | .call _ _ _ _ hx _ _ _ _ _ => exact hsafe.2 s hs (Or.inl (by rw [hx]; simp))
    | .ctrl _ _ _ hx _ _ _ => exact hsafe.2 s hs (Or.inl (by rw [hx]; simp))
    | .ctrlAfterCall _ _ hx _ => exact hsafe.2 s hs (Or.inl (by rw [hx]; simp))
  · -- the views published since the last call
    intro htop ha' j v₀ hlast hv
    match h with
    | .init _ _ hx _ _ =>
      obtain ⟨hv0, _, _⟩ := hI.wf.init hx
      simp [hv0] at hv
    | .call .. => simp at htop
    | .ctrl _ x₂ _ hx ha hc _ =>
      obtain ⟨hrec, hv₂, hk₂, hl₂, _, _⟩ := complete_fields hc
      obtain ⟨hrec', hv', hk', hl', _⟩ := receive_fields inp (publish K x)
      have hlen := hI.wf.top hx
      have hne : x.phase ≠ .init := by rw [hx]; simp
      have hcx := hI.comp hne ha
      change K.ctrl x.record s at hs
      change x₂.kLast < j at hlast
      change x₂.v[j]? = some v₀ at hv
      change ∃ r, K.view r = v₀ ∧ K.Active r ∧ K.C r ∧ K.Win (x₂.k + 1 - j) r s
      rw [hl₂, hl'] at hlast
      rw [hv₂, hv'] at hv
      rw [hk₂, hk']
      change (x.v ++ [K.view x.record])[j]? = some v₀ at hv
      change x.kLast < j at hlast
      change ∃ r, K.view r = v₀ ∧ K.Active r ∧ K.C r ∧ K.Win (x.k + 1 - j) r s
      by_cases hlt : j < x.v.length
      · rw [List.getElem?_append_left hlt] at hv
        obtain ⟨r, hr, hra, hrc, hw⟩ := hI.views hx ha j v₀ hlast hv
        refine ⟨r, hr, hra, hrc, ?_⟩
        rw [show x.k + 1 - j = (x.k - j) + 1 by omega]
        exact K.win_snoc hw ha hs
      · have hle : j < x.v.length + 1 := by
          have := (List.getElem?_eq_some_iff.1 hv).1; simpa using this
        have heq : j = x.v.length := by omega
        rw [heq, List.getElem?_append_right (Nat.le_refl _)] at hv
        simp at hv
        refine ⟨x.record, hv, ha, hcx, ?_⟩
        rw [heq, hlen, show x.k + 1 - x.k = 0 + 1 by omega]
        exact K.win_snoc rfl ha hs
    | .ctrlAfterCall _ _ hx _ =>
      obtain ⟨hlen, hkl, _⟩ := hI.wf.after hx
      change x.kLast < j at hlast
      change x.v[j]? = some v₀ at hv
      have := (List.getElem?_eq_some_iff.1 hv).1
      omega

variable (K) in
/-- The clause at every instant of an operation from the start of the contract: at every instant of
an operation after the first, and at every active instant of the first, the initialization. -/
def SegCompliant (j : Nat) (σ : Segment W S) : Prop :=
  ∀ τ : σ.Inst, (0 < j ∨ K.Active (σ.pt τ).2) → K.C (σ.pt τ).2

variable (K) in
/-- The clause at every instant of every operation of a list, from the start of the contract. -/
def Compliant (xs : List (Op K P × Segment W S)) : Prop :=
  ∀ j (h : j < xs.length), SegCompliant K j xs[j].2

theorem compliant_append {xs : List (Op K P × Segment W S)} {a : Op K P × Segment W S}
    (h₁ : Compliant K xs) (h₂ : SegCompliant K xs.length a.2) : Compliant K (xs ++ [a]) := by
  intro j hj
  by_cases hlt : j < xs.length
  · rw [List.getElem_append_left hlt]; exact h₁ j hlt
  · have heq : j = xs.length := by simp at hj; omega
    subst heq
    simpa using h₂

/-- An operation that Algorithm 1 invokes, whose instants are effects from the record: under A1 and
A2, the clause holds at each of its instants, from the start of the contract. -/
theorem segment_compliant (hA1 : ch.Sound) (hA2 : Coverage K E) {w : W} {x : Vars K P}
    {inp : Input K P} {o : Op K P} {κ : S → Vars K P} {j : Nat} (hI : Inv K ch x)
    (hj : 0 < j → x.phase ≠ .init) (h : Next K ch πK x inp o κ) (σ : Segment W S)
    (he : ∀ τ, E.op o w x.record (σ.pt τ).1 (σ.pt τ).2) : SegCompliant K j σ := by
  have hsafe := next_safe hA1 hI h
  intro τ hor
  have hD := hA2.op hsafe.1 (he τ)
  rcases hor with hpos | ha
  · exact hsafe.2 _ hD (Or.inl (hj hpos))
  · exact hsafe.2 _ hD (Or.inr ha)

/-- Every execution keeps the invariant, starts with the initialization, and complies, under A1 and
A2. -/
theorem exec_inv (hA1 : ch.Sound) (hA2 : Coverage K E) {s₀ : S} {w : W} {x : Vars K P}
    {xs : List (Op K P × Segment W S)} (h : Exec K ch πK E s₀ w x xs) :
    Inv K ch x ∧ (x.phase = .init ↔ xs = []) ∧ Compliant K xs := by
  induction h with
  | start => exact ⟨inv_start s₀, by simp [start], fun j h => by simp at h⟩
  | @step w x xs inp o κ σ l _ hn _ he ih =>
    obtain ⟨hI, hph, hC⟩ := ih
    have hsafe := next_safe hA1 hI hn
    have hj : 0 < xs.length → x.phase ≠ .init := fun hpos hinit => by
      have := hph.1 hinit; subst this; simp at hpos
    refine ⟨next_inv hA1 hI hn (hA2.op hsafe.1 (he l)), ⟨fun h' => absurd h' (next_phase hn _),
      fun h' => by simp at h'⟩, compliant_append hC ?_⟩
    exact segment_compliant hA1 hA2 hI hj hn σ he

/-- **Theorem 1 (Anytime compliance to the contract).** Under A1 (sound checking) and A2 (coverage),
for any sequence of requests and proposed proofs, every execution of Algorithms 1–2 (A4) satisfies the
clause at every instant of every operation from the start of the contract: at every instant of the
operations after the initialization, and at every active instant of the initialization, closing
included, and throughout an operation that never returns. A3 is not a hypothesis: the Airlock starts
only once the checker has accepted the certificate as a proof of it. -/
theorem anytime_compliance (hA1 : ch.Sound) (hA2 : Coverage K E) {s₀ : S}
    {xs : List (Op K P × Segment W S)} (hX : Execution K ch πK E s₀ xs) :
    ∀ j (h : j < xs.length) (τ : xs[j].2.Inst),
      (0 < j ∨ K.Active (xs[j].2.pt τ).2) → K.C (xs[j].2.pt τ).2 := by
  cases hX with
  | returned hx => exact (exec_inv hA1 hA2 hx).2.2
  | @running w x xs inp o κ σ hx hn _ he =>
    obtain ⟨hI, hph, hC⟩ := exec_inv hA1 hA2 hx
    have hj : 0 < xs.length → x.phase ≠ .init := fun hpos hinit => by
      have := hph.1 hinit; subst this; simp at hpos
    exact compliant_append hC (segment_compliant hA1 hA2 hI hj hn σ he)

end

end PC2
