module

public import ArtinMatthews.SourceQuadraticSmallError
public import ArtinMatthews.SourceQuadraticDualFiniteErrors
public import ArtinMatthews.SourceQuadraticNormalizedResidue
public import ArtinMatthews.SourceQuadraticFullResidue
public import ArtinMatthews.SourceQuadraticPairConductor
public import ArtinMatthews.SourceQuadraticSignedResidueBound
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "C" => sourceQuadraticConductor F S₀ hζ
local notation "Bad" => sourceQuadraticBlockBadIdeal F S₀

/-- The finite actual Small residue has the combined-modulus half-coefficient form. -/
theorem sourceQuadraticOriginalSmallResidue_eq_halfCoefficient {M H : ℝ}
    (hM : 0 < M) (hH : 0 ≤ H) (g e : E) (hmc : IsCoprime (Bad * I g) (C e)) :
    sourceQuadraticOriginalSmallResidue F S₀ hζ M H g e =
      sourceQuadraticSmallResidueFactor F M * quadraticHeckeCoprimeDensity F (C e) *
        quadraticHeckeCoprimeDensity F (Bad * I g) *
          ∑ a ∈ quadraticHeckeCoprimeCutoff F (Bad * I g) H,
            quadraticHeckeHalfCoefficient F (Ψ e) a := by
  have hs := sourceQuadraticSmallResidue_combinedModulus F S₀ hζ g e hmc hM H
  rw [sourceQuadraticSmallRows_tsum F S₀ hH g (fun J =>
    (Ψ e).allCoefficient J * ((dedekindZeta_residue F : ℂ) *
      (Real.sqrt (M / (Ideal.absNorm J : ℝ)) : ℂ) *
        ((1 / 2 : ℂ) * mellin (fun t : ℝ => (sourceQuadraticB2Bump t : ℂ)) (1 / 2)) *
        quadraticHeckeCoprimeDensity F (Bad * I g * C e)))] at hs
  unfold sourceQuadraticOriginalSmallResidue
  rw [show sourceQuadraticBlockProfile = (fun t : ℝ => (sourceQuadraticB2Bump t : ℂ)) from rfl]
  simpa only [sourceQuadraticBlockSquareModulus, sourceQuadraticBlockModulus,
    sourcePrimeExponentIdeal_norm] using hs

/-- The actual two finite residues have precisely the radical-cancellation difference. -/
theorem sourceQuadraticPair_actualResidueDifference {M H : ℝ} (hM : 0 < M) (hH : 0 ≤ H)
    (b c g : E) (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    sourceQuadraticDualDivisorResidue F S₀ hζ M H g ((b-g)+(c-g)) -
        sourceQuadraticOriginalSmallResidue F S₀ hζ M H g ((b-g)+(c-g)) =
      sourceQuadraticSmallResidueFactor F M * quadraticHeckeCoprimeDensity F (C ((b-g)+(c-g))) *
        sourceQuadraticHalfResidueDifference F S₀ hζ H g ((b-g)+(c-g)) := by
  have hmc : IsCoprime (Bad * I g) (C ((b-g)+(c-g))) := by
    rw [sourceQuadraticPairConductor_eq_product F S₀ hζ b c g hb hc hg hclass]
    exact sourceQuadratic_commonModulus_coprime_residualProduct F S₀ b c g hb hc
  rw [sourceQuadraticDualDivisorResidue_eq_halfCoefficient F S₀ hζ hM H g ((b-g)+(c-g)),
    sourceQuadraticOriginalSmallResidue_eq_halfCoefficient F S₀ hζ hM hH g ((b-g)+(c-g)) hmc]
  unfold sourceQuadraticHalfResidueDifference sourceQuadraticBlockModulus
  ring

/-- The signed difference of the literal Full and Small residues over all common pairs. -/
def sourceQuadraticActualSignedResidueBlock (M H : ℝ) (cols : Finset E)
    (u : E → ℂ) (g : E) : ℂ :=
  ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
    star (u p.1) * u p.2 *
      (sourceQuadraticDualDivisorResidue F S₀ hζ M H g ((p.1-g)+(p.2-g)) -
        sourceQuadraticOriginalSmallResidue F S₀ hζ M H g ((p.1-g)+(p.2-g)))

theorem sourceQuadraticActualSignedResidueBlock_eq_normalized {M H : ℝ}
    (hM : 0 < M) (hH : 0 ≤ H) (cols : Finset E) (u : E → ℂ) (g : E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b)
    (hclass : ∀ b ∈ cols, ∀ c ∈ cols, b ⊓ c = g →
      sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    sourceQuadraticActualSignedResidueBlock F S₀ hζ M H cols u g =
      sourceQuadraticNormalizedResidueBlock F S₀ hζ M H cols u g := by
  unfold sourceQuadraticActualSignedResidueBlock sourceQuadraticNormalizedResidueBlock
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpair, hg⟩ := Finset.mem_filter.mp hp
  obtain ⟨hb, hc⟩ := Finset.mem_product.mp hpair
  rw [sourceQuadraticPair_actualResidueDifference F S₀ hζ hM hH p.1 p.2 g
    (hcols p.1 hb) (hcols p.2 hc) hg (hclass p.1 hb p.2 hc hg)]
  ring

/-- GL7.3 for the signed, actual Full and Small residues, including the diagonal pairs. -/
theorem sourceQuadraticActualSignedResidueBlock_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ cBound : ℝ, 0 < cBound ∧ ∀ M P H : ℝ, 1 ≤ M → 1 ≤ P → 1 ≤ H → H ≤ M →
      ∀ (cols : Finset E) (u : E → ℂ) (g : E),
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ P) →
      (∀ b ∈ cols, ∀ c ∈ cols, b ⊓ c = g →
        sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) →
      ‖sourceQuadraticActualSignedResidueBlock F S₀ hζ M H cols u g‖ ≤
        cBound * (q g : ℝ) ^ 4 * (M * P) ^ ε *
          (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P) *
            ∑ b ∈ cols, ‖u b‖ ^ 2 := by
  obtain ⟨cBound, hc, hbound⟩ := sourceQuadraticNormalizedResidueBlock_bound F S₀ hζ htrace hE ε hε
  refine ⟨cBound, hc, ?_⟩
  intro M P H hM hP hH hHM cols u g hcols hclass
  rw [sourceQuadraticActualSignedResidueBlock_eq_normalized F S₀ hζ
    (zero_lt_one.trans_le hM) (zero_le_one.trans hH) cols u g (fun b hb => (hcols b hb).1) hclass]
  exact hbound M P H hM hP hH hHM cols u g hcols hclass

omit [IsTotallyComplex F] in
private theorem squarefreeCutoff_empty {H : ℝ} (hH : H < 1) :
    quadraticHeckeSquarefreeCutoff F H = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro J hJ
  obtain ⟨hsf, hn⟩ := (mem_quadraticHeckeSquarefreeCutoff F).1 hJ
  have hnorm : (1 : ℝ) ≤ Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hsf.ne_zero)
  exact (not_le.mpr hH) (hnorm.trans hn)

/-- Both exact squarefree residue cutoffs vanish below norm one. -/
theorem sourceQuadraticActualSignedResidueBlock_eq_zero_of_lt_one {M H : ℝ}
    (hM : 0 < M) (hH : 0 ≤ H) (hH1 : H < 1) (cols : Finset E) (u : E → ℂ) (g : E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b)
    (hclass : ∀ b ∈ cols, ∀ c ∈ cols, b ⊓ c = g →
      sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) :
    sourceQuadraticActualSignedResidueBlock F S₀ hζ M H cols u g = 0 := by
  rw [sourceQuadraticActualSignedResidueBlock_eq_normalized F S₀ hζ hM hH cols u g hcols hclass]
  simp only [sourceQuadraticNormalizedResidueBlock, sourceQuadraticHalfResidueDifference,
    quadraticHeckeCoprimeCutoff, squarefreeCutoff_empty F hH1, Finset.filter_empty,
    Finset.sum_empty, zero_mul, sub_self, mul_zero, Finset.sum_const_zero]

/-- The signed-residue estimate retains every nonnegative original cutoff. -/
theorem sourceQuadraticActualSignedResidueBlock_nonneg_cutoff_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ cBound : ℝ, 0 < cBound ∧ ∀ M P H : ℝ, 1 ≤ M → 1 ≤ P → 0 ≤ H → H ≤ M →
      ∀ (cols : Finset E) (u : E → ℂ) (g : E),
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ P) →
      (∀ b ∈ cols, ∀ c ∈ cols, b ⊓ c = g →
        sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) →
      ‖sourceQuadraticActualSignedResidueBlock F S₀ hζ M H cols u g‖ ≤
        cBound * (q g : ℝ) ^ 4 * (M * P) ^ ε *
          (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P) *
            ∑ b ∈ cols, ‖u b‖ ^ 2 := by
  obtain ⟨cBound, hc, hbound⟩ := sourceQuadraticActualSignedResidueBlock_bound F S₀ hζ htrace hE ε hε
  refine ⟨cBound, hc, ?_⟩
  intro M P H hM hP hH hHM cols u g hcols hclass
  by_cases hH1 : 1 ≤ H
  · exact hbound M P H hM hP hH1 hHM cols u g hcols hclass
  · rw [sourceQuadraticActualSignedResidueBlock_eq_zero_of_lt_one F S₀ hζ
      (zero_lt_one.trans_le hM) hH (lt_of_not_ge hH1) cols u g
      (fun b hb => (hcols b hb).1) hclass, norm_zero]
    positivity

/-- The original dyadic column ceiling contributes only a fixed scalar factor. -/
theorem sourceQuadraticActualSignedResidueBlock_annular_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ cBound : ℝ, 0 < cBound ∧ ∀ M P H : ℝ, 1 ≤ M → 1 ≤ P → 0 ≤ H → H ≤ M →
      ∀ (cols : Finset E) (u : E → ℂ) (g : E),
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ 2 * P) →
      (∀ b ∈ cols, ∀ c ∈ cols, b ⊓ c = g →
        sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) →
      ‖sourceQuadraticActualSignedResidueBlock F S₀ hζ M H cols u g‖ ≤
        cBound * (q g : ℝ) ^ 4 * (M * P) ^ ε *
          (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P) *
            ∑ b ∈ cols, ‖u b‖ ^ 2 := by
  obtain ⟨cBound, hc, hbound⟩ :=
    sourceQuadraticActualSignedResidueBlock_nonneg_cutoff_bound F S₀ hζ htrace hE ε hε
  refine ⟨((2 : ℝ) ^ ε * 2) * cBound, by positivity, ?_⟩
  intro M P H hM hP hH hHM cols u g hcols hclass
  have hb := hbound M (2 * P) H hM (by linarith) hH hHM cols u g hcols hclass
  have hpow : (M * (2 * P)) ^ ε = (2 : ℝ) ^ ε * (M * P) ^ ε := by
    rw [show M * (2 * P) = 2 * (M * P) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ M * P)]
  have hshape : Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * (2 * P) ≤
      2 * (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P) := by
    have ha : 0 ≤ Real.sqrt M * H ^ (α - 1 / 2) := by positivity
    nlinarith
  calc
    _ ≤ cBound * (q g : ℝ) ^ 4 * (M * (2 * P)) ^ ε *
        (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * (2 * P)) *
          ∑ b ∈ cols, ‖u b‖ ^ 2 := hb
    _ = cBound * (q g : ℝ) ^ 4 * ((2 : ℝ) ^ ε * (M * P) ^ ε) *
        (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * (2 * P)) *
          ∑ b ∈ cols, ‖u b‖ ^ 2 := by rw [hpow]
    _ ≤ cBound * (q g : ℝ) ^ 4 * ((2 : ℝ) ^ ε * (M * P) ^ ε) *
        (2 * (Real.sqrt M * H ^ (α - 1 / 2) + Real.sqrt (M / H) * P)) *
          ∑ b ∈ cols, ‖u b‖ ^ 2 := by gcongr
    _ = _ := by ring

end
end ArtinMatthews.SourceEulerAssembly
