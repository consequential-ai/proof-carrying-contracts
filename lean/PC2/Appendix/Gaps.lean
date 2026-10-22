import PC2.Basic

/-!
# Appendix D: time between operations

A gap of at most `t₀` after each routine is included in the operation: the extended tool `T'` runs the
routine, then waits, and its model is `D_T'(i, s, s'') = ∃ z, D_T(i, s, z) ∧ D_idle(t₀, z, s'')`
(Eq. extended-model). The extended contract `𝒦'` is a contract, so every result of the paper applies to
it, with its own assumptions.
-/

namespace PC2

variable {S : Type}

/-- The extended tool `T'`, for the model `gap` of what outside changes can do within `t₀`. -/
def Tool.extend (T : Tool S) (gap : S → S → Prop) : Tool S where
  Inp := T.Inp
  D i s s'' := ∃ z, T.D i s z ∧ gap z s''

/-- The extended contract `𝒦'`: the tools and the control step extended by the gap. -/
def Contract.extend (K : Contract S) (gap : S → S → Prop) : Contract S where
  C := K.C
  V := K.V
  view := K.view
  Name := K.Name
  tools l := (K.tools l).extend gap
  ctrl s s'' := ∃ z, K.ctrl s z ∧ gap z s''
  stop := K.stop

variable (T : Tool S) (gap : S → S → Prop)

/-- The model of `T'` admits every state the model of `T` admits (the gap may be zero). -/
theorem extend_mono (hrefl : ∀ z, gap z z) {i : T.Inp} {s s' : S} (h : T.D i s s') :
    (T.extend gap).D i s s' :=
  ⟨s', h, hrefl s'⟩

/-- `T'` is enabled exactly where `T` is. -/
theorem extend_en (hrefl : ∀ z, gap z z) (i : T.Inp) (s : S) :
    (T.extend gap).En i s ↔ T.En i s :=
  ⟨fun ⟨_, z, hz, _⟩ => ⟨z, hz⟩, fun ⟨z, hz⟩ => ⟨z, z, hz, hrefl z⟩⟩

/-- `(T|Pre)' = T'|Pre`: a goal-gated settlement stays goal-gated. -/
theorem extend_restrict (Pre : T.Inp → S → Prop) (i : T.Inp) (s s'' : S) :
    ((T.restrict Pre).extend gap).D i s s'' ↔ ((T.extend gap).restrict Pre).D i s s'' :=
  ⟨fun ⟨z, ⟨hp, hz⟩, hg⟩ => ⟨hp, z, hz, hg⟩, fun ⟨hp, z, hz, hg⟩ => ⟨z, ⟨hp, hz⟩, hg⟩⟩

/-- With no gap (`t₀ = 0`, the gap model is the identity), `T' = T`. -/
theorem extend_zero (hid : ∀ z s'', gap z s'' ↔ z = s'') (i : T.Inp) (s s'' : S) :
    (T.extend gap).D i s s'' ↔ T.D i s s'' :=
  ⟨fun ⟨z, hz, hg⟩ => by rw [← (hid z s'').1 hg]; exact hz,
   fun h => ⟨s'', h, (hid s'' s'').2 rfl⟩⟩

end PC2
