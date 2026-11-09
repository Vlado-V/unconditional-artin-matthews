module

public import ArtinMatthews.SourceKPReflectedRetainedProfiles
public import ArtinMatthews.SourceKPReflectedBranchArithmetic
public import ArtinMatthews.SixthExteriorPowerClassesFinite


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed finite seed coefficients are kept separate from the
arithmetic majorant. The scaling variable is the actual norm-one
sixth orbit of the normalized numerator. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic
open SourcePhysical SourceReflection SourceEulerAssembly
open scoped NumberField Classical BigOperators ContDiff
noncomputable section
set_option quotPrecheck false

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "X" => ExteriorUnitSixthClasses S
local notation "Q" => SWholePowerClasses K 6 S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "Whole" => SWholeUnits K S
local notation "N" => SNormOne K S
local notation "D" => sWholeDiagonal K S
local notation "sc" => sLocalPositiveScaling K hζ S
local notation "C" => sourceReflectionExponentSixthClass K S₀ hζ
local notation "Idx[" f "]" => SourceReflectionTermIndex K S₀ f

def sourceKPReflectedBranchDilation (ε : X) (f : Finset PE) (t : ℝ) (i : Idx[f]) : Whole :=
  D (sourceReflectionRetainedNumeratorUnit K S₀ hζ i.1.val i.2.1 i.2.2.val ε) * sc t

theorem sourceKPReflectedBranchDilation_norm (ε : X) (f : Finset PE) {t : ℝ} (ht : 0 < t)
    (i : Idx[f]) :
    sLocalNorm K S (sourceKPReflectedBranchDilation K hζ S₀ ε f t i) =
      sourceReflectionTermLength K S₀ i.1.val i.2.1 i.2.2.val * t := by
  rw [sourceKPReflectedBranchDilation, sLocalNorm_mul,
    sourceReflectionRetainedNumeratorUnit_norm K S₀ hζ, sLocalPositiveScaling_norm K hζ S ht]

theorem sourceKPReflectedBranchDilation_orbit (ε : X) (f : Finset PE) (d : E)
    (t : ℝ) (i : SourceReflectionSupportedTermIndex K S₀ f d) (γ : Γ) (n : N) :
    (((n*γ.val : N) : Whole) * sourceKPReflectedBranchDilation K hζ S₀ ε f t i.val) =
      D (sourceKPReflectedNumerator K hζ S₀ f d i ε γ) * ((n : Whole)*sc t) := by
  rw [sourceKPReflectedNumerator_diagonal]
  change ((n : Whole)*(γ.val : Whole)) *
    (sourceKPReflectedNumeratorBase K hζ S₀ f d i ε*sc t) = _
  ac_rfl

variable {J : Ideal (𝓞 K)} {T : ℝ}
local notation "Label[" p "]" => SourceKPReflectedRetainedLabel K hζ S₀ (p).R (p).M
attribute [local instance] sourceKPReflectedRetainedLabel_fintype
local notation "cs" => sourceKPReflectedRetainedSeedScalar K hζ S₀
local notation "BA" => sourceKPReflectedBranchArithmetic K hζ S₀

def sourceKPReflectedBranchCoefficient
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (hT : 2 < T)
    (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (u ε : X) (h d : E) (f : Finset PE) (i : Idx[f]) (l : Label[p]) : ℂ :=
  BA hS η hJ u ε h d f i l.2.2 * cs hS hJ hT p (l.1,l.2.1)

def sourceKPReflectedBranchCoefficientMajorant
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (hJ : J ≠ ⊥) (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT) : ℝ :=
  1 + ∑ l : Label[p], ‖cs hS hJ hT p (l.1,l.2.1)‖

theorem sourceKPReflectedBranchCoefficientMajorant_pos
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (hJ : J ≠ ⊥) (hT : 2 < T) (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT) :
    0 < sourceKPReflectedBranchCoefficientMajorant K hζ S₀ hS hJ hT p := by
  unfold sourceKPReflectedBranchCoefficientMajorant
  exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

theorem sourceKPReflectedBranchCoefficient_norm_le
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥) (hT : 2 < T)
    (p : SourceKPPositiveSeedData K hζ S₀ hS hJ hT)
    (u ε : X) (h d : E) (f : Finset PE) (i : Idx[f]) (l : Label[p]) :
    ‖sourceKPReflectedBranchCoefficient K hζ S₀ hS η hJ hT p u ε h d f i l‖ ≤
      sourceKPReflectedBranchCoefficientMajorant K hζ S₀ hS hJ hT p *
        sourceReflectionDirichletTerm K S₀ f 0 i := by
  have ha := sourceKPReflectedBranchArithmetic_norm_le K hζ S₀ hS η hJ u ε h d f i l.2.2
  have hs : ‖cs hS hJ hT p (l.1,l.2.1)‖ ≤
      sourceKPReflectedBranchCoefficientMajorant K hζ S₀ hS hJ hT p := by
    unfold sourceKPReflectedBranchCoefficientMajorant
    exact (Finset.single_le_sum (fun l _ => norm_nonneg (cs hS hJ hT p (l.1,l.2.1)))
      (Finset.mem_univ l)).trans (le_add_of_nonneg_left zero_le_one)
  unfold sourceKPReflectedBranchCoefficient
  rw [norm_mul,mul_comm]
  exact mul_le_mul hs ha (norm_nonneg _) (sourceKPReflectedBranchCoefficientMajorant_pos K hζ S₀ hS hJ hT p).le

end
end ArtinMatthews
