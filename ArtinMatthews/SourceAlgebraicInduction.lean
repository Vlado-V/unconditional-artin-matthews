module

public import Mathlib.RepresentationTheory.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Algebraic induction with left covariance and right translation.
A subgroup factorization and an intersection-fixed value construct
a spherical section by a choice of factors, with exact independence. -/

namespace ArtinMatthews
noncomputable section

variable {R G V : Type*} [Semiring R] [Group G] [AddCommMonoid V] [Module R V]
    (B : Subgroup G) (ρ : Representation R B V)

def sourceAlgebraicInducedSpace : Submodule R (G → V) where
  carrier := {f | ∀ (b : B) g, f (b.val * g) = ρ b (f g)}
  zero_mem' b g := (map_zero (ρ b)).symm
  add_mem' := by
    intro f f' hf hf' b g
    change f (b.val * g) + f' (b.val * g) = ρ b (f g + f' g)
    rw [hf b g, hf' b g, map_add]
  smul_mem' := by
    intro a f hf b g
    change a • f (b.val * g) = ρ b (a • f g)
    rw [hf b g, map_smul]

theorem sourceAlgebraicInducedSpace_covariant (f : sourceAlgebraicInducedSpace B ρ) (b : B) (g : G) :
    f.val (b.val * g) = ρ b (f.val g) := f.property b g

def sourceAlgebraicInducedRepresentation : Representation R G (sourceAlgebraicInducedSpace B ρ) where
  toFun g :=
    { toFun := fun f => ⟨fun h => f.val (h * g), by
        intro b h
        change f.val ((b.val * h) * g) = ρ b (f.val (h * g))
        rw [mul_assoc]
        exact sourceAlgebraicInducedSpace_covariant B ρ f b (h * g)⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext h
    change f.val (h * 1) = f.val h
    rw [mul_one]
  map_mul' g k := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext h
    change f.val (h * (g * k)) = f.val ((h * g) * k)
    rw [mul_assoc]

theorem sourceAlgebraicInducedRepresentation_apply (g h : G) (f : sourceAlgebraicInducedSpace B ρ) :
    (sourceAlgebraicInducedRepresentation B ρ g f).val h = f.val (h * g) := rfl

variable (C : Subgroup G) (v : V)
    (hI : ∀ g : G, ∃ (b : B) (c : C), g = b.val * c.val)
    (hfix : ∀ (b : B) (c : C), b.val = c.val → ρ b v = v)

include hfix in
private theorem sourceAlgebraicSpherical_factor_eq {b b' : B} {c c' : C}
    (h : b.val * c.val = b'.val * c'.val) : ρ b v = ρ b' v := by
  let b₀ := b'⁻¹ * b
  let c₀ := c' * c⁻¹
  have he : b₀.val = c₀.val := by
    change b'.val⁻¹ * b.val = c'.val * c.val⁻¹
    calc
      _ = b'.val⁻¹ * ((b.val * c.val) * c.val⁻¹) := by rw [mul_inv_cancel_right]
      _ = b'.val⁻¹ * ((b'.val * c'.val) * c.val⁻¹) := by rw [h]
      _ = _ := by rw [← mul_assoc, inv_mul_cancel_left]
  have hb : b' * b₀ = b := by dsimp only [b₀]; rw [mul_inv_cancel_left]
  calc
    ρ b v = ρ (b' * b₀) v := by rw [hb]
    _ = ρ b' (ρ b₀ v) := by rw [map_mul]; rfl
    _ = ρ b' v := by rw [hfix b₀ c₀ he]

private def sourceAlgebraicSphericalValue (g : G) : V := ρ ((hI g).choose) v

include hfix in
private theorem sourceAlgebraicSphericalValue_factor {g : G} {b : B} {c : C}
    (hg : g = b.val * c.val) : sourceAlgebraicSphericalValue B ρ C v hI g = ρ b v :=
  sourceAlgebraicSpherical_factor_eq B ρ C v hfix ((hI g).choose_spec.choose_spec.symm.trans hg)

def sourceAlgebraicSphericalSection : sourceAlgebraicInducedSpace B ρ :=
  ⟨sourceAlgebraicSphericalValue B ρ C v hI, by
    intro b g
    obtain ⟨b₀, c, hg⟩ := hI g
    have h : b.val * g = (b * b₀).val * c.val := by
      rw [hg]
      exact (mul_assoc _ _ _).symm
    change sourceAlgebraicSphericalValue B ρ C v hI (b.val * g) =
      ρ b (sourceAlgebraicSphericalValue B ρ C v hI g)
    rw [sourceAlgebraicSphericalValue_factor B ρ C v hI hfix h,
      sourceAlgebraicSphericalValue_factor B ρ C v hI hfix hg, map_mul]
    rfl⟩

theorem sourceAlgebraicSphericalSection_factor {g : G} {b : B} {c : C}
    (hg : g = b.val * c.val) :
    (sourceAlgebraicSphericalSection B ρ C v hI hfix).val g = ρ b v :=
  sourceAlgebraicSphericalValue_factor B ρ C v hI hfix hg

theorem sourceAlgebraicSphericalSection_one :
    (sourceAlgebraicSphericalSection B ρ C v hI hfix).val 1 = v := by
  rw [sourceAlgebraicSphericalSection_factor B ρ C v hI hfix
    (b := 1) (c := 1) (one_mul (1 : G)).symm, map_one]
  rfl

theorem sourceAlgebraicSphericalSection_right (c : C) :
    sourceAlgebraicInducedRepresentation B ρ c.val (sourceAlgebraicSphericalSection B ρ C v hI hfix) =
      sourceAlgebraicSphericalSection B ρ C v hI hfix := by
  apply Subtype.ext
  funext g
  rw [sourceAlgebraicInducedRepresentation_apply]
  obtain ⟨b, c₀, hg⟩ := hI g
  have hc : g * c.val = b.val * (c₀ * c).val := by
    rw [hg]
    exact mul_assoc _ _ _
  rw [sourceAlgebraicSphericalSection_factor B ρ C v hI hfix hc,
    sourceAlgebraicSphericalSection_factor B ρ C v hI hfix hg]

end
end ArtinMatthews
