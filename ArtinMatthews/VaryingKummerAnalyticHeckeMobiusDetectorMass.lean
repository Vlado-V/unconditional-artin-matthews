module

public import ArtinMatthews.VaryingKummerAnalyticHeckeGaussianDetector
public import ArtinMatthews.VaryingKummerAnalyticHeckeIdealMobius
public import ArtinMatthews.VaryingKummerAnalyticHeckeGaussianDetectorGrid
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusMass
public import ArtinMatthews.VaryingKummerAnalyticMixedPartialDedekind
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Transfer the proved actual ideal Möbius square mass to the class
partition used by the genuine Hecke conductor detector. No mass estimate
or residue-family injection is supplied by the caller. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def mobiusClassWeight (D : ℝ) (c : ClassGroup (𝓞 K))
    (J : integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)) : ℂ :=
  HeckeIdealMobius.truncated K D
    ((integralFractionalIdealsEquiv K).symm ⟨J.val,J.property.1⟩).val

theorem nonzeroIdeal_norm_equiv (J : integralFractionalIdeals K) :
    (Ideal.absNorm ((integralFractionalIdealsEquiv K).symm J).val : ℝ) =
      (FractionalIdeal.absNorm J.val.val : ℝ) := by
  have h (I : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
      (FractionalIdeal.absNorm ((integralFractionalIdealsEquiv K) I).val.val : ℝ) =
        (Ideal.absNorm I.val : ℝ) := by
    change (FractionalIdeal.absNorm (I.val : FractionalIdeal (𝓞 K)⁰ K) : ℝ) = _
    rw [FractionalIdeal.coeIdeal_absNorm]
    rfl
  rw [← h,Equiv.apply_symm_apply]

theorem exists_mobiusClassWeight_mass_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D σ X : ℝ)
      (B : ∀ c : ClassGroup (𝓞 K),
        Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c))),
      0 < X → 1+3*ε ≤ 2*σ →
      (∀ c, ∀ J ∈ B c, X ≤ (FractionalIdeal.absNorm J.val.val : ℝ)) →
      coefficientClassDirichletMass K B (mobiusClassWeight K D) σ ≤ C*X^(1+3*ε-2*σ) := by
  obtain ⟨C,hC,hbound⟩ := HeckeIdealMobius.exists_truncated_weighted_square_mass K ε hε
  refine ⟨C,hC,?_⟩
  intro D σ X B hX hσ hB
  let e := (rayIdealClassPartitionEquiv K 1).trans (integralFractionalIdealsEquiv K).symm
  let S := (Finset.univ.sigma B).map e.toEmbedding
  have hn (c : ClassGroup (𝓞 K))
      (J : integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)) :
      (Ideal.absNorm (e ⟨c,J⟩).val : ℝ) = (FractionalIdeal.absNorm J.val.val : ℝ) := by
    exact nonzeroIdeal_norm_equiv K ⟨J.val,J.property.1⟩
  have H := hbound D σ X S hX hσ (by
    intro I hI
    obtain ⟨⟨c,J⟩,hJ,rfl⟩ := Finset.mem_map.mp hI
    change X ≤ (Ideal.absNorm (e ⟨c,J⟩).val : ℝ)
    rw [hn]
    exact hB c J (Finset.mem_sigma.mp hJ).2)
  dsimp only [S] at H
  rw [Finset.sum_map,Finset.sum_sigma] at H
  convert H using 1
  unfold coefficientClassDirichletMass
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro J _
  change (‖HeckeIdealMobius.truncated K D (e ⟨c,J⟩).val‖ *
    (FractionalIdeal.absNorm J.val.val : ℝ)^(-σ))^2 =
      ‖HeckeIdealMobius.truncated K D (e ⟨c,J⟩).val‖^2 *
        (Ideal.absNorm (e ⟨c,J⟩).val : ℝ)^(-2*σ)
  rw [hn]
  rw [mul_pow,← Real.rpow_mul_natCast (fractionalIdeal_absNorm_pos J.val).le (-σ) 2]
  congr 2
  ring

theorem exists_mobius_detector_bounded_height_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D σ X U Y Z δ : ℝ),
      1 ≤ X → 1 ≤ U → 0 ≤ Y → 0 < Z → 0 < δ → 1+3*ε ≤ 2*σ →
      ∀ (T : Finset (IdealConductorModulus K))
        (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
        (B : ∀ c : ClassGroup (𝓞 K),
          Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c))),
        (∀ M ∈ T, (Ideal.absNorm M.val : ℝ) ≤ U) →
        (∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue) →
        (∀ c, ∀ J ∈ B c, Z ≤ (FractionalIdeal.absNorm J.val.val : ℝ)) →
        (∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val : ℝ) ≤ X) →
        (∑ M ∈ T, (((A M).image (fun ψ => ψ.coefficient)).filter
          (fun a => ∃ t : ℝ, |t| ≤ Y ∧ δ ≤
            ‖coefficientClassDirichletPolynomial K a B (mobiusClassWeight K D) σ t‖)).card : ℝ) ≤
          C*(2*Y+4)*(X+U^2)*(1+(Real.log X)^2)*Z^(1+3*ε-2*σ)/δ^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_mobiusClassWeight_mass_bound K ε hε
  refine ⟨heckeGaussianWindowConstant K*C,mul_pos (heckeGaussianWindowConstant_pos K) hC,?_⟩
  intro D σ X U Y Z δ hX hU hY hZ hδ hσ T A B hT hA hB hB'
  have H := actualHecke_coefficientFamily_bounded_height_count K hU hX hY T hT A hA B hB'
    (mobiusClassWeight K D) σ δ hδ
  apply H.trans
  have hmass := hbound D σ Z B hZ hσ hB
  have hfac : 0 ≤ (2*Y+4)*heckeGaussianWindowConstant K*(X+U^2)*(1+(Real.log X)^2)/δ^2 := by
    have hc := (heckeGaussianWindowConstant_pos K).le
    positivity
  convert mul_le_mul_of_nonneg_left hmass hfac using 1 <;> ring

end
end ArtinMatthews.VaryingKummerAnalytic
