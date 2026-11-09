module

public import ArtinMatthews.SourceKPPhysicalResidualFiniteSum
public import ArtinMatthews.SourceReflectionPositiveFiniteTwist
public import ArtinMatthews.SourceKPRetainedSeedExterior
public import ArtinMatthews.SourceThetaArchMellin


set_option backward.privateInPublic true
@[expose] public section

/-! The positive physical test is the literal finite sum of the source
Fourier twists and retained seed translates. The mask allows a fixed
active branch of that same finite sum. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain SourceReflection SourcePhysical
open scoped NumberField Classical BigOperators MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "U" => SWholeUnits K S
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "V" => InfinitePlace K

attribute [local instance] positiveTwistLabelFintype

theorem sourceKPSLocalProjectiveDiagonalLift_finite (x : U) :
    (sourceSLocalProjectiveDiagonalLift K S hζ x).2 = D (sourceKPRetainedDiagonalUnit K S x.2) := by
  change D (sourceKPIdeleFiniteUnit K (sourceSLocalIdeleLift K S x)) = _
  apply congrArg D
  apply Units.ext
  apply FiniteAdeleRing.ext
  intro P
  change (sourceKPIdeleFiniteCoordinate K P (sourceSLocalIdeleLift K S x) : P.adicCompletion K) =
    (sourceKPRetainedUnitAt K P (sourceKPRetainedDiagonalUnit K S x.2) : P.adicCompletion K)
  by_cases hP : P ∈ S
  · rw [sourceSLocalIdeleLift_finite_in K S x ⟨P,hP⟩,
      sourceKPRetainedDiagonalUnit_unitAt_mem K S x.2 ⟨P,hP⟩]
  · rw [sourceSLocalIdeleLift_finite_out K S x P hP,
      sourceKPRetainedDiagonalUnit_unitAt_notMem K S x.2 P hP]

variable (e : SourcePrimeExponents K S₀) (R M : ↥(sourceHilbertSet K S₀) → ℕ)
include hζ S₀ e R M
local notation "H" => SourceReflectionPositiveTwistLabels K S₀ e
local notation "I" => SourceKPRetainedSeedIndex K S R M
local notation "tw" => sourceReflectionPositiveTwistWeight K hζ S₀ e
local notation "tu" => sourceReflectionPositiveTwistAdele K hζ S₀ e
local notation "sw" => sourceKPRetainedSeedWeight K S R M
local notation "st" => sourceKPRetainedSeedTranslate K hζ S R M

def sourceKPPositivePhysicalTranslate (q₀ : Gf) (p : H × I) : Gf :=
  Nf (tu p.1) * st q₀ p.2

def sourceKPPositivePhysicalTranslateWeight (mask : H → ℂ) (p : H × I) : ℂ :=
  mask p.1 * tw p.1 * sw p.2

def sourceKPPositivePhysicalFiniteValue (ε : V → Bool) {T : ℝ} (hT : 1 ≤ T)
    (q₀ : Gf) (mask : H → ℂ) (weight : U → ℂ) (x : U) : ℂ :=
  weight x * (sourceKPCuspResidualFourierValue K hζ 1 hT q₀)⁻¹ *
    sourceKPPhysicalResidualFiniteValue K hζ S ε hT
      (sourceKPPositivePhysicalTranslate K hζ S₀ e R M q₀)
      (sourceKPPositivePhysicalTranslateWeight K hζ S₀ e R M mask) x

def sourceKPPositivePhysicalFiniteCoefficient {T : ℝ} (hT : 1 ≤ T)
    (q₀ : Gf) (mask : H → ℂ) (m : Kˣ) (x : U) : ℂ :=
  ∑ h : H, mask h * tw h *
    sourceKPRetainedSeedFourierAt K hζ S R M hT 1 q₀
      (sourceKPCuspResidualUnitTranslate K hζ m
        (D (sourceKPRetainedDiagonalUnit K S x.2) * Nf (tu h)))

def sourceKPPositivePhysicalFiniteTerm (ε : V → Bool) {T : ℝ} (hT : 1 ≤ T)
    (q₀ : Gf) (mask : H → ℂ) (weight : U → ℂ) (m : Kˣ) (x : U) : ℂ :=
  weight x * (sourceKPCuspResidualFourierValue K hζ 1 hT q₀)⁻¹ *
    sourceKPPositivePhysicalFiniteCoefficient K hζ S₀ e R M hT q₀ mask m x *
    sourceKPResidualArchAngular K ε m *
    ∏ v : V, sourceThetaArchFactor K v (4*Real.pi) ((sWholeDiagonal K S m*x).1 v)

theorem sourceKPPositivePhysicalFiniteValue_hasSum (ε : V → Bool) {T : ℝ} (hT : 1 ≤ T)
    (q₀ : Gf) (mask : H → ℂ) (weight : U → ℂ) (x : U) :
    HasSum (fun m : Kˣ => sourceKPPositivePhysicalFiniteTerm K hζ S₀ e R M ε hT q₀ mask weight m x)
      (sourceKPPositivePhysicalFiniteValue K hζ S₀ e R M ε hT q₀ mask weight x) := by
  let a := sourceKPPositivePhysicalTranslateWeight K hζ S₀ e R M mask
  let t := sourceKPPositivePhysicalTranslate K hζ S₀ e R M q₀
  let b := weight x * (sourceKPCuspResidualFourierValue K hζ 1 hT q₀)⁻¹
  let f (m : Kˣ) := sourceKPResidualArchAngular K ε m *
    ∏ v : V, sourceThetaArchFactor K v (4*Real.pi) ((sWholeDiagonal K S m*x).1 v)
  have h := (sourceKPPhysicalResidualFiniteValue_hasSum K hζ S ε hT t a x).mul_left b
  apply h.congr_fun
  intro m
  have he (p : H × I) :
      sourceKPPhysicalResidualBesselTerm K hζ S ε hT
        ((sourceSLocalProjectiveDiagonalLift K S hζ x).2 * t p) m x =
      sourceKPCuspResidualFourierValue K hζ 1 hT
        (sourceKPCuspResidualUnitTranslate K hζ m
          (D (sourceKPRetainedDiagonalUnit K S x.2) * Nf (tu p.1)) * st q₀ p.2) * f m := by
    unfold sourceKPPhysicalResidualBesselTerm
    rw [sourceKPSLocalProjectiveDiagonalLift_finite K hζ S₀ x]
    unfold t sourceKPPositivePhysicalTranslate sourceKPCuspResidualUnitTranslate f
    simp only [mul_assoc]
    rfl
  change b * sourceKPPositivePhysicalFiniteCoefficient K hζ S₀ e R M hT q₀ mask m x * _ * _ =
    b * ∑ p : H × I, a p * sourceKPPhysicalResidualBesselTerm K hζ S ε hT
      ((sourceSLocalProjectiveDiagonalLift K S hζ x).2 * t p) m x
  simp_rw [he, ← mul_assoc _ _ (f m), ← Finset.sum_mul]
  rw [Fintype.sum_prod_type]
  unfold sourceKPPositivePhysicalFiniteCoefficient sourceKPRetainedSeedFourierAt
  simp_rw [Finset.mul_sum]
  have hh (h : H) (i : I) :
      a (h,i) = mask h * tw h * sw i := rfl
  simp only [hh]
  unfold f
  simp only [mul_assoc]
  simp_rw [← Finset.mul_sum]
  ring

end
end ArtinMatthews
