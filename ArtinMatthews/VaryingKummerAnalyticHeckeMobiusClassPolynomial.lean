module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusPowerAnnuli
public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusDetectorMass
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite class decomposition of the smoothed ideal detector. The
class supports and weights are constructed from the actual ideal norm. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Complex
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def heckeClassIndexEquiv :
    (Σ c : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)) ≃
      {I : Ideal (𝓞 K) // I ≠ ⊥} :=
  (rayIdealClassPartitionEquiv K 1).trans (integralFractionalIdealsEquiv K).symm

def heckeClassNormCutoff (R : ℝ) (c : ClassGroup (𝓞 K)) :
    Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)) :=
  (((HeckeIdealMobius.normCutoff K R).subtype (fun I => I ≠ ⊥)).map
    (heckeClassIndexEquiv K).symm.toEmbedding).preimage
      (fun J : integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) =>
        (⟨c,J⟩ : Σ d : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K 1 d)))
      (by
        intro J _ L _ h
        exact Subtype.ext (congrArg (fun p : Σ d : ClassGroup (𝓞 K),
          integralIdealClassFiber (rayClassFractionalRepresentative K 1 d) => p.2.val) h))

theorem heckeClassIndexEquiv_norm (c : ClassGroup (𝓞 K))
    (J : integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)) :
    (Ideal.absNorm (heckeClassIndexEquiv K ⟨c,J⟩).val : ℝ) =
      (FractionalIdeal.absNorm J.val.val : ℝ) :=
  nonzeroIdeal_norm_equiv K ⟨J.val,J.property.1⟩

theorem mem_heckeClassNormCutoff {R : ℝ} (hR : 0 ≤ R) (c : ClassGroup (𝓞 K))
    (J : integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)) :
    J ∈ heckeClassNormCutoff K R c ↔ (FractionalIdeal.absNorm J.val.val : ℝ) ≤ R := by
  have hp : J ∈ heckeClassNormCutoff K R c ↔
      (⟨c,J⟩ : Σ d : ClassGroup (𝓞 K), integralIdealClassFiber (rayClassFractionalRepresentative K 1 d)) ∈
        ((HeckeIdealMobius.normCutoff K R).subtype (fun I => I ≠ ⊥)).map
          (heckeClassIndexEquiv K).symm.toEmbedding := Finset.mem_preimage
  rw [hp,Finset.mem_map]
  constructor
  · rintro ⟨I,hI,he⟩
    have he' : heckeClassIndexEquiv K ⟨c,J⟩ = I := by
      rw [← he]
      exact (heckeClassIndexEquiv K).apply_symm_apply I
    have hn := (HeckeIdealMobius.mem_normCutoff K hR I.val).mp (Finset.mem_subtype.mp hI)
    rw [← he',heckeClassIndexEquiv_norm] at hn
    exact hn
  · intro hJ
    refine ⟨heckeClassIndexEquiv K ⟨c,J⟩,Finset.mem_subtype.mpr ?_,?_⟩
    · apply (HeckeIdealMobius.mem_normCutoff K hR _).mpr
      rwa [heckeClassIndexEquiv_norm]
    · exact (heckeClassIndexEquiv K).symm_apply_apply ⟨c,J⟩

theorem sum_heckeClassNormCutoff (R : ℝ) (F : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ) :
    (∑ c : ClassGroup (𝓞 K), ∑ J ∈ heckeClassNormCutoff K R c,
      F (heckeClassIndexEquiv K ⟨c,J⟩)) =
      ∑ I ∈ (HeckeIdealMobius.normCutoff K R).subtype (fun I => I ≠ ⊥), F I := by
  have he : Finset.univ.sigma (heckeClassNormCutoff K R) =
      ((HeckeIdealMobius.normCutoff K R).subtype (fun I => I ≠ ⊥)).map
        (heckeClassIndexEquiv K).symm.toEmbedding := by
    unfold heckeClassNormCutoff
    apply Finset.sigma_preimage_mk_of_subset
    exact Finset.subset_univ _
  have hs := Finset.sum_sigma Finset.univ (heckeClassNormCutoff K R)
    (fun p => F (heckeClassIndexEquiv K p))
  rw [he] at hs
  rw [← hs,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro I _
  exact congrArg F ((heckeClassIndexEquiv K).apply_symm_apply I)

def heckeClassNormAnnulus (L R : ℝ) (c : ClassGroup (𝓞 K)) :
    Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)) :=
  (heckeClassNormCutoff K R c).filter (fun J => L < (FractionalIdeal.absNorm J.val.val : ℝ))

def mobiusSmoothedClassWeight (D Y : ℝ) (c : ClassGroup (𝓞 K))
    (J : integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)) : ℂ :=
  mobiusClassWeight K D c J *
    Complex.exp (-((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)/(Y : ℂ))

theorem mobiusSmoothedClassWeight_mass_le (D Y σ : ℝ) (hY : 0 < Y)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c))) :
    coefficientClassDirichletMass K B (mobiusSmoothedClassWeight K D Y) σ ≤
      coefficientClassDirichletMass K B (mobiusClassWeight K D) σ := by
  unfold coefficientClassDirichletMass
  apply Finset.sum_le_sum
  intro c _
  apply Finset.sum_le_sum
  intro J _
  have hN := fractionalIdeal_absNorm_pos J.val
  have he : ‖Complex.exp (-((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)/(Y : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_neg,← Complex.ofReal_div,Complex.norm_exp,Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hN.le) hY.le)
  simp only [mobiusSmoothedClassWeight,norm_mul]
  gcongr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (norm_nonneg (mobiusClassWeight K D c J))

namespace EvenIdealRayCharacter
variable {K} {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M)

theorem mobiusClassPolynomial_eq_finiteNormAnnulus (D Y L R σ t : ℝ) (hR : 0 ≤ R) :
    coefficientClassDirichletPolynomial K ψ.coefficient (heckeClassNormAnnulus K L R)
      (mobiusSmoothedClassWeight K D Y) σ t =
    finiteNormAnnulus (HeckeIdealMobius.normCutoff K R) (fun I => (Ideal.absNorm I : ℝ)) L R
      (fun I => ψ.mobiusConvolutionCoefficient D I*(Ideal.absNorm I : ℂ)^(-((σ : ℂ)+(t : ℂ)*Complex.I))*
        Complex.exp (-(Ideal.absNorm I : ℂ)/(Y : ℂ))) := by
  let T (I : Ideal (𝓞 K)) :=
    ψ.mobiusConvolutionCoefficient D I*(Ideal.absNorm I : ℂ)^(-((σ : ℂ)+(t : ℂ)*Complex.I))*
      Complex.exp (-(Ideal.absNorm I : ℂ)/(Y : ℂ))
  have H := sum_heckeClassNormCutoff K R (fun I => if L < (Ideal.absNorm I.val : ℝ) then T I.val else 0)
  have hleft : coefficientClassDirichletPolynomial K ψ.coefficient (heckeClassNormAnnulus K L R)
      (mobiusSmoothedClassWeight K D Y) σ t =
      ∑ c : ClassGroup (𝓞 K), ∑ J ∈ heckeClassNormCutoff K R c,
        if L < (Ideal.absNorm (heckeClassIndexEquiv K ⟨c,J⟩).val : ℝ)
          then T (heckeClassIndexEquiv K ⟨c,J⟩).val else 0 := by
    unfold coefficientClassDirichletPolynomial coefficientClassPolynomial heckeClassNormAnnulus
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro J _
    rw [heckeClassIndexEquiv_norm]
    split_ifs
    · have hNc : (Ideal.absNorm (heckeClassIndexEquiv K ⟨c,J⟩).val : ℂ) =
          ((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ) := by
        exact_mod_cast heckeClassIndexEquiv_norm K c J
      dsimp only [T,mobiusSmoothedClassWeight,mobiusClassWeight,mobiusConvolutionCoefficient]
      rw [hNc,heckeVerticalPhase_eq_cpow (fractionalIdeal_absNorm_pos J.val)]
      have hc := ψ.allCoefficient_underlying ⟨J.val,J.property.1⟩
      change ψ.allCoefficient (heckeClassIndexEquiv K ⟨c,J⟩).val = _ at hc
      rw [hc]
      have hi : (heckeClassIndexEquiv K ⟨c,J⟩).val =
          ((integralFractionalIdealsEquiv K).symm ⟨J.val,J.property.1⟩).val := rfl
      rw [hi]
      ring
    · rfl
  rw [hleft,H,Finset.sum_subtype_eq_sum_filter
    (fun I : Ideal (𝓞 K) => if L < (Ideal.absNorm I : ℝ) then T I else 0)]
  unfold finiteNormAnnulus
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  have hN := (HeckeIdealMobius.mem_normCutoff K hR I).mp hI
  change (if I ≠ ⊥ then if L < (Ideal.absNorm I : ℝ) then T I else 0 else 0) =
    if L < (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ R then T I else 0
  by_cases hI0 : I=⊥
  · subst I
    have hz : T ⊥ = 0 := by
      dsimp only [T]
      rw [show ψ.mobiusConvolutionCoefficient D ⊥=0 from ψ.mobiusConvolutionCoefficient_zero D,zero_mul,zero_mul]
    rw [hz]
    simp only [ne_eq,not_true_eq_false,ite_self]
  · simp only [ne_eq,hI0,not_false_eq_true,ite_true,hN,and_true]

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
