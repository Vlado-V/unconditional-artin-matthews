module

public import ArtinMatthews.SourceKPPositiveOrbitTwist
public import ArtinMatthews.SourceReflectionSignedExteriorProduct
public import ArtinMatthews.SourceKPReflectedFiniteSplitActual
public import ArtinMatthews.SourceReflectionPositiveLiftComparison
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Selecting the nonzero residues at the active primes turns the
literal finite Fourier-label sum into the signed exterior product. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic QuadraticWeil SourceEulerAssembly
open scoped NumberField AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "R[" P "]" => (𝓞 K) ⧸ HeightOneSpectrum.asIdeal (Subtype.val P)
local notation "H" => SourceReflectionPositiveTwistLabels K S₀
local notation "C" => sourceReflectionTameFourierCoefficient K hζ S₀
local notation "X" => sourceReflectionPositiveLocalTranslation K hζ S₀
local notation "V" => sourceReflectionSignedExteriorWeylValue K S₀ hζ hS
local notation "F" => sourceReflectionSignedExteriorLocal K S₀ hζ hS
local notation "tu" => sourceReflectionPositiveTwistAdele K hζ S₀
local notation "wt" => sourceReflectionPositiveTwistWeight K hζ S₀
local notation "mask" => sourceKPPositivePhysicalActiveMask K S₀

attribute [local instance] positiveResidueField positiveTwistResidueFintype positiveTwistLabelFintype

private theorem localLabelSum (e : E) (active : Finset Pr) (ν : Kˣ) (P : Pr) (hP : P ∈ e.support) :
    (∑ z : R[P], if z ≠ 0 ↔ P ∈ active then
      C P (sourceReflectionPositiveIndex (e P)) z * V P ν (X P z) else 0) = F P e active ν := by
  by_cases ha : P ∈ active
  · simp only [ha, iff_true]
    unfold sourceReflectionSignedExteriorLocal
    rw [ite_eq_left ha]
    let g (z : R[P]) := C P (sourceReflectionPositiveIndex (e P)) z * V P ν (X P z)
    calc
      _ = ∑ z : {z : R[P] // z ≠ 0}, g z.val := by
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype ((Finset.univ : Finset R[P]).filter (· ≠ 0))
          (fun z => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) g
      _ = _ := by
        refine Fintype.sum_equiv unitsEquivNeZero.symm _ _ (fun z => ?_)
        dsimp only [g]
        rw [← sourceReflectionPositiveLocalTranslation_unit K hζ S₀ P (unitsEquivNeZero.symm z)]
        rfl
  · simp only [ha, iff_false, not_ne_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [sourceReflectionPositiveLocalTranslation_zero,
      sourceReflectionSignedExteriorLocal_inactive K S₀ hζ hS P e active ν ha, ite_eq_left hP,
      sourceReflectionSignedExteriorWeylValue_zero_shift]
    rfl

theorem sourceKPReflectedC1ResidueProduct_eq (e : E) (active U : Finset Pr) (ν : Kˣ)
    (ha : active ⊆ e.support) (he : e.support ⊆ U)
    (hord : ∀ P : Pr, P ∉ U → exteriorPrincipalValuation P.val ν = 0) :
    (∑ h : H e, mask e active h * wt e h *
      ∏ P ∈ U, V P ν (tu e h P.val)) =
      sourceReflectionSignedExteriorProduct K S₀ hζ hS e active ν := by
  let q := ∏ P ∈ U \ e.support, V P ν 0
  let g (P : e.support) (z : R[P.val]) := if z ≠ 0 ↔ P.val ∈ active then
    C P.val (sourceReflectionPositiveIndex (e P.val)) z * V P.val ν (X P.val z) else 0
  have hsplit (h : H e) : (∏ P ∈ U, V P ν (tu e h P.val)) =
      q * ∏ P : e.support, V P.val ν (X P.val (h P)) := by
    rw [← Finset.prod_sdiff he]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro P hP
      have hp : P.val ∉ e.support.image Subtype.val := by
        intro hmem
        obtain ⟨Q,hQ,hQP⟩ := Finset.mem_image.mp hmem
        exact (Finset.mem_sdiff.mp hP).2 (Subtype.ext hQP ▸ hQ)
      rw [sourceReflectionPositiveTwistAdele_zero_of_not_mem_row K hζ S₀ e h P.val hp]
    · rw [← Finset.prod_coe_sort e.support (fun P => V P ν (tu e h P.val))]
      apply Finset.prod_congr rfl
      intro P _
      exact congrArg (V P.val ν) (sourceReflectionPositiveTwistAdele_at_row K hζ S₀ e h P)
  have hlabel (h : H e) : mask e active h * wt e h *
      (∏ P ∈ U, V P ν (tu e h P.val)) = q * ∏ P : e.support, g P (h P) := by
    by_cases hsel : ∀ P : e.support, h P ≠ 0 ↔ P.val ∈ active
    · rw [sourceKPPositivePhysicalActiveMask, ite_eq_left hsel, one_mul, hsplit, sourceReflectionPositiveTwistWeight]
      rw [mul_left_comm, ← Finset.prod_mul_distrib]
      apply congrArg (q * ·)
      apply Finset.prod_congr rfl
      intro P _
      exact (ite_eq_left (hsel P)).symm
    · obtain ⟨P,hP⟩ := not_forall.mp hsel
      have hz : g P (h P) = 0 := ite_eq_right hP
      rw [sourceKPPositivePhysicalActiveMask, ite_eq_right hsel, zero_mul, zero_mul,
        Finset.prod_eq_zero (Finset.mem_univ P) hz, mul_zero]
  simp_rw [hlabel]
  rw [← Finset.mul_sum, ← Fintype.prod_sum g,
    sourceReflectionSignedExteriorProduct_eq_prod K S₀ hζ hS e active ν U he (ha.trans he) hord,
    ← Finset.prod_sdiff he]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro P hP
    have hn := (Finset.mem_sdiff.mp hP).2
    rw [sourceReflectionSignedExteriorLocal_inactive K S₀ hζ hS P e active ν (fun h => hn (ha h)),
      ite_eq_right hn, one_mul, sourceReflectionSignedExteriorWeylValue_zero_shift]
  · rw [← Finset.prod_coe_sort e.support (F · e active ν)]
    apply Finset.prod_congr rfl
    intro P _
    exact localLabelSum K hζ S₀ hS e active ν P.val P.property

end
end ArtinMatthews
