module

public import ArtinMatthews.SourceKPCompactUpper
public import ArtinMatthews.SourceKPCompactDiagonal
public import ArtinMatthews.SourceKPCompactWeyl
public import ArtinMatthews.SourceKubotaCocycle


set_option backward.privateInPublic true
@[expose] public section

/-! The compact cochain solves the actual cocycle equation on every
pair of integral matrices. Propagation uses the proved full cocycle
and the genuine unit-preserving matrix reduction. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section
variable {F Γ A : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ] [CommGroup A]
    (ν : Valuation F Γ) (B : Fˣ →* (Fˣ →* A))

def sourceKPCompactRightGood (h : GL (Fin 2) F) : Prop :=
  ∀ g, SourceKPIntegralMatrix ν g →
    sourceKPCompactPhase ν B (g * h) =
      sourceKPCompactPhase ν B g * sourceKPCompactPhase ν B h * sourceKP2Multiplier B g h

theorem sourceKPCompactRightGood_mul
    (hC : ∀ g h k : GL (Fin 2) F,
      sourceKP2Multiplier B g h * sourceKP2Multiplier B (g * h) k =
        sourceKP2Multiplier B g (h * k) * sourceKP2Multiplier B h k)
    {h k : GL (Fin 2) F} (hh : SourceKPIntegralMatrix ν h)
    (hH : sourceKPCompactRightGood ν B h) (hK : sourceKPCompactRightGood ν B k) :
    sourceKPCompactRightGood ν B (h * k) := by
  intro g hg
  rw [← mul_assoc g h k, hK (g * h) (sourceKPIntegralMatrix_mul ν hg hh), hH g hg, hK h hh]
  calc
    _ = (sourceKPCompactPhase ν B g * sourceKPCompactPhase ν B h * sourceKPCompactPhase ν B k) *
        (sourceKP2Multiplier B g h * sourceKP2Multiplier B (g * h) k) := by ac_rfl
    _ = _ := by rw [hC]; ac_rfl

theorem sourceKPCompactPhase_mul
    (hdiag : ∀ x, B x x = 1) (hcube : ∀ x y, B x y ^ 3 = 1)
    (hminus : ∀ x, B x (sourceMinusOneUnit F) = 1)
    (hsteinberg : ∀ x : Fˣ, ∀ hx : 1 - (x : F) ≠ 0, B x (Units.mk0 _ hx) = 1)
    (hunit : ∀ a b : Fˣ, ν (a : F) = 1 → ν (b : F) = 1 → B a b = 1)
    (hprincipal : ∀ a b : Fˣ, ν ((b : F) - 1) < 1 → B a b = 1)
    (g h : GL (Fin 2) F) (hg : SourceKPIntegralMatrix ν g) (hh : SourceKPIntegralMatrix ν h) :
    sourceKPCompactPhase ν B (g * h) =
      sourceKPCompactPhase ν B g * sourceKPCompactPhase ν B h * sourceKP2Multiplier B g h := by
  have hC := sourceKP2Multiplier_cocycle B hdiag hminus hsteinberg
  have hU (x : F) (hx : ν x ≤ 1) : sourceKPCompactRightGood ν B (sourceGL2Upper x) :=
    fun z hz => sourceKPCompactPhase_right_upper ν B hprincipal z hz x hx
  have hD (u : Fˣ) (hu : ν (u : F) = 1) : sourceKPCompactRightGood ν B (sourceGL2Diagonal u) :=
    fun z hz => sourceKPCompactPhase_right_diagonal ν B hdiag hunit z hz u hu
  have hS (u : Fˣ) (hu : ν (u : F) = 1) :
      sourceKPCompactRightGood ν B (GeneralLinearGroup.scalar (Fin 2) u) :=
    fun z hz => sourceKPCompactPhase_right_scalar ν B hdiag hcube hunit z hz u hu
  have hW : sourceKPCompactRightGood ν B (sourceGL2Weyl : GL (Fin 2) F) :=
    sourceKPCompactPhase_right_weyl ν B hdiag hminus hunit
  have htri (z : GL (Fin 2) F) (hz : SourceKPIntegralMatrix ν z) (hc : z 1 0 = 0) :
      sourceKPCompactRightGood ν B z := by
    obtain ⟨x, u, d, hx, hu, hd, hfactor⟩ := sourceKPIntegralMatrix_triangular_factor ν z hz hc
    rw [hfactor]
    have hXu := sourceKPIntegralMatrix_mul ν (sourceKPIntegralMatrix_upper ν x hx)
      (sourceKPIntegralMatrix_diagonal ν u hu)
    exact sourceKPCompactRightGood_mul ν B hC hXu
      (sourceKPCompactRightGood_mul ν B hC (sourceKPIntegralMatrix_upper ν x hx) (hU x hx) (hD u hu)) (hS d hd)
  have hwf (z : GL (Fin 2) F) (hz : SourceKPIntegralMatrix ν z) (hc : ν (z 1 0) = 1) :
      sourceKPCompactRightGood ν B z := by
    obtain ⟨b, x, hb, hb0, hx, hfactor⟩ := sourceKPIntegralMatrix_weyl_factor ν z hz hc
    rw [hfactor]
    have hbw := sourceKPIntegralMatrix_mul ν hb (sourceKPIntegralMatrix_weyl ν)
    exact sourceKPCompactRightGood_mul ν B hC hbw
      (sourceKPCompactRightGood_mul ν B hC hb (htri b hb hb0) hW) (hU x hx)
  have hhGood : sourceKPCompactRightGood ν B h := by
    by_cases hc0 : h 1 0 = 0
    · exact htri h hh hc0
    by_cases hc : ν (h 1 0) = 1
    · exact hwf h hh hc
    have hd := (sourceKPIntegralMatrix_bottom_unit ν hh).resolve_left hc
    let h' := h * (sourceGL2Weyl : GL (Fin 2) F)
    have hh' : SourceKPIntegralMatrix ν h' :=
      sourceKPIntegralMatrix_mul ν hh (sourceKPIntegralMatrix_weyl ν)
    have hh'c : ν (h' 1 0) = 1 :=
      (congrArg ν (sourceGL2_right_weyl_bottom_left h)).trans hd
    have he : h = h' * sourceGL2Weyl := by
      change h = (h * (sourceGL2Weyl : GL (Fin 2) F)) * sourceGL2Weyl
      rw [mul_assoc, sourceGL2Weyl_square, mul_one]
    rw [he]
    exact sourceKPCompactRightGood_mul ν B hC hh' (hwf h' hh' hh'c) hW
  exact hhGood g hg

end
end ArtinMatthews
