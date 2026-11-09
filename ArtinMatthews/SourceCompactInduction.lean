module

public import ArtinMatthews.SourceAlgebraicInduction


set_option backward.privateInPublic true
@[expose] public section

/-! An induced section supported on a subgroup product, with its
factor independence and right invariance proved directly. -/

namespace ArtinMatthews
open scoped Classical
noncomputable section

variable {R G V : Type*} [Semiring R] [Group G] [AddCommMonoid V] [Module R V]
    (B : Subgroup G) (ρ : Representation R B V) (C : Subgroup G) (v : V)

def sourceCompactInducedFactorable (g : G) : Prop :=
  ∃ (b : B) (c : C), g = b.val * c.val

def sourceCompactInducedValue (g : G) : V :=
  if h : sourceCompactInducedFactorable B C g then ρ h.choose v else 0

variable (hfix : ∀ (b : B) (c : C), b.val = c.val → ρ b v = v)

include hfix in
theorem sourceCompactInducedFactor_eq {b b' : B} {c c' : C}
    (he : b.val * c.val = b'.val * c'.val) : ρ b v = ρ b' v := by
  let b₀ := b'⁻¹ * b
  let c₀ := c' * c⁻¹
  have hi : b₀.val = c₀.val := by
    change b'.val⁻¹ * b.val = c'.val * c.val⁻¹
    calc
      _ = b'.val⁻¹ * ((b.val * c.val) * c.val⁻¹) := by rw [mul_inv_cancel_right]
      _ = b'.val⁻¹ * ((b'.val * c'.val) * c.val⁻¹) := by rw [he]
      _ = _ := by rw [← mul_assoc, inv_mul_cancel_left]
  have hb : b' * b₀ = b := by dsimp only [b₀]; rw [mul_inv_cancel_left]
  calc
    ρ b v = ρ (b' * b₀) v := by rw [hb]
    _ = ρ b' (ρ b₀ v) := by rw [map_mul]; rfl
    _ = ρ b' v := by rw [hfix b₀ c₀ hi]

include hfix in
theorem sourceCompactInducedValue_factor {g : G} {b : B} {c : C}
    (he : g = b.val * c.val) : sourceCompactInducedValue B ρ C v g = ρ b v := by
  have hg : sourceCompactInducedFactorable B C g := ⟨b,c,he⟩
  rw [sourceCompactInducedValue, dite_eq_left hg]
  exact sourceCompactInducedFactor_eq B ρ C v hfix
    (hg.choose_spec.choose_spec.symm.trans he)

theorem sourceCompactInducedValue_zero {g : G}
    (hg : ¬sourceCompactInducedFactorable B C g) :
    sourceCompactInducedValue B ρ C v g = 0 := by
  rw [sourceCompactInducedValue, dite_eq_right hg]

include hfix in
theorem sourceCompactInducedValue_left (b : B) (g : G) :
    sourceCompactInducedValue B ρ C v (b.val*g) = ρ b (sourceCompactInducedValue B ρ C v g) := by
  by_cases hg : sourceCompactInducedFactorable B C g
  · obtain ⟨b₀,c,he⟩ := hg
    have hb : b.val*g = (b*b₀).val*c.val := by rw [he]; exact (mul_assoc _ _ _).symm
    rw [sourceCompactInducedValue_factor B ρ C v hfix hb,
      sourceCompactInducedValue_factor B ρ C v hfix he, map_mul]
    rfl
  · have hb : ¬sourceCompactInducedFactorable B C (b.val*g) := by
      rintro ⟨b₀,c,he⟩
      apply hg
      refine ⟨b⁻¹*b₀,c,?_⟩
      change g = (b.val⁻¹*b₀.val)*c.val
      calc
        g = b.val⁻¹*(b.val*g) := by rw [inv_mul_cancel_left]
        _ = b.val⁻¹*(b₀.val*c.val) := by rw [he]
        _ = _ := (mul_assoc _ _ _).symm
    rw [sourceCompactInducedValue_zero B ρ C v hb,
      sourceCompactInducedValue_zero B ρ C v hg, map_zero]

include hfix in
theorem sourceCompactInducedValue_right (c : C) (g : G) :
    sourceCompactInducedValue B ρ C v (g*c.val) = sourceCompactInducedValue B ρ C v g := by
  by_cases hg : sourceCompactInducedFactorable B C g
  · obtain ⟨b,c₀,he⟩ := hg
    have hc : g*c.val = b.val*(c₀*c).val := by rw [he]; exact mul_assoc _ _ _
    rw [sourceCompactInducedValue_factor B ρ C v hfix hc,
      sourceCompactInducedValue_factor B ρ C v hfix he]
  · have hc : ¬sourceCompactInducedFactorable B C (g*c.val) := by
      rintro ⟨b,c₀,he⟩
      apply hg
      refine ⟨b,c₀*c⁻¹,?_⟩
      change g = b.val*(c₀.val*c.val⁻¹)
      calc
        g = (g*c.val)*c.val⁻¹ := by rw [mul_inv_cancel_right]
        _ = (b.val*c₀.val)*c.val⁻¹ := by rw [he]
        _ = _ := mul_assoc _ _ _
    rw [sourceCompactInducedValue_zero B ρ C v hc,
      sourceCompactInducedValue_zero B ρ C v hg]

def sourceCompactInducedSection : sourceAlgebraicInducedSpace B ρ :=
  ⟨sourceCompactInducedValue B ρ C v, sourceCompactInducedValue_left B ρ C v hfix⟩

theorem sourceCompactInducedSection_factor {g : G} {b : B} {c : C}
    (he : g = b.val*c.val) :
    (sourceCompactInducedSection B ρ C v hfix).val g = ρ b v :=
  sourceCompactInducedValue_factor B ρ C v hfix he

theorem sourceCompactInducedSection_one :
    (sourceCompactInducedSection B ρ C v hfix).val 1 = v := by
  rw [sourceCompactInducedSection_factor B ρ C v hfix
    (b := 1) (c := 1) (one_mul (1 : G)).symm, map_one]
  rfl

theorem sourceCompactInducedSection_right (c : C) :
    sourceAlgebraicInducedRepresentation B ρ c.val (sourceCompactInducedSection B ρ C v hfix) =
      sourceCompactInducedSection B ρ C v hfix := by
  apply Subtype.ext
  funext g
  exact sourceCompactInducedValue_right B ρ C v hfix c g

end
end ArtinMatthews
