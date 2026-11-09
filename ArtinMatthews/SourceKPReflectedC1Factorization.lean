module

public import ArtinMatthews.SourceKPReflectedC1ResidueProduct
public import ArtinMatthews.SourceKPPositivePhysicalFinite
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedResidualTensor


set_option backward.privateInPublic true
@[expose] public section

/-! The original active residue and retained seed sum factors into the
signed exterior product and the actual finite retained Jacquet tensor. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix StandardAdelic QuadraticWeil SourceEulerAssembly
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "C₁" => sourceKPCuspResidualFourierValue K hζ (1 : Kˣ)
local notation "H" => SourceReflectionPositiveTwistLabels K S₀
local notation "I" => SourceKPRetainedSeedIndex K S
local notation "L" => sourceKPLocalCompactProductLift K hζ S
local notation "word" => sourceKPReflectedC1RetainedWord K hζ S₀
local notation "b₀" => fun f d => sourcePrimeExponentUnit K hζ S₀ (sourceReflectionActiveExponents K S₀ f+d)
local notation "q₀" => fun a : A => Prod.snd (sourceKPAdelicRootSupportTuple K hζ 1 a S)
local notation "mask" => sourceKPPositivePhysicalActiveMask K S₀
local notation "tw" => sourceReflectionPositiveTwistWeight K hζ S₀
local notation "tu" => sourceReflectionPositiveTwistAdele K hζ S₀
local notation "sw" => sourceKPRetainedSeedWeight K S
local notation "weyl" => sourceKPReflectedC1WeylPhase K hζ S₀
local notation "phase" => sourceKPReflectedC1ExteriorPhase K hζ S₀

attribute [local instance] positiveTwistLabelFintype

private theorem weighted_term_factor (a h p u v : ℂ) :
    (a*h)*(p*u*v) = (p*(a*v))*(h*u) := by
  ac_rfl

private theorem factor_two_finite_sums {ι κ : Type} [Fintype ι] [Fintype κ]
    (p : ℂ) (u : ι → ℂ) (v : κ → ℂ) :
    (∑ i, ∑ j, (p*u i)*v j) = (p*∑ i, u i)*(∑ j, v j) := by
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

def sourceKPReflectedC1RetainedSum {T : ℝ} (hT : 2 < T) (m : Kˣ) (x : SWholeUnits K S)
    (R M₀ : S → ℕ) (a₀ : A) : ℂ :=
  ∑ i : I R M₀, sw R M₀ i * C₁ (one_le_two.trans hT.le) (L (word m x R M₀ i a₀)).2

def sourceKPReflectedC1ActiveCoefficient {T : ℝ} (hT : 2 < T)
    (m : Kˣ) (f : Finset Pr) (d e : E) (x : SWholeUnits K S) (R M₀ : S → ℕ) (a₀ : A) : ℂ :=
  ∑ p : H e × I R M₀,
    sourceKPPositivePhysicalTranslateWeight K hζ S₀ e R M₀ (mask e (f ∪ d.support)) p *
      C₁ (one_le_two.trans hT.le) (sourceKPCuspResidualUnitTranslate K hζ m
        (sourceKPReflectedHorizontalFiber K hζ S (b₀ f d)
          (sourceKPPositivePhysicalTranslate K hζ S₀ e R M₀ (q₀ a₀) p) x))

theorem sourceKPReflectedC1ActiveCoefficient_factor
    (hS : standardWeilBadPlaces K ⊆ S) {T : ℝ} (hT : 2 < T)
    (m : Kˣ) (f : Finset Pr) (d e : E) (ha : f ∪ d.support ⊆ e.support)
    (x : SWholeUnits K S) (R M₀ : S → ℕ) (a₀ : A) :
    let b := b₀ f d
    sourceKPReflectedC1ActiveCoefficient K hζ S₀ hT m f d e x R M₀ a₀ =
      weyl b x * phase e m b *
        sourceReflectionSignedExteriorProduct K S₀ hζ hS e (f ∪ d.support) (m*(b⁻¹)^2) *
        sourceKPReflectedC1RetainedSum K hζ S₀ hT m x R M₀ a₀ := by
  intro b
  let U := sourceKPReflectedC1ExteriorPrimes K S₀ e m b
  let act := f ∪ d.support
  let p := weyl b x * phase e m b
  let E₀ (h : H e) := mask e act h * tw e h * ∏ P ∈ U,
    sourceReflectionSignedExteriorWeylValue K S₀ hζ hS P (m*(b⁻¹)^2) (tu e h P.val)
  let I₀ (i : I R M₀) := sw R M₀ i * C₁ (one_le_two.trans hT.le) (L (word m x R M₀ i a₀)).2
  have hsum : (∑ h, E₀ h) = sourceReflectionSignedExteriorProduct K S₀ hζ hS e act (m*(b⁻¹)^2) :=
    sourceKPReflectedC1ResidueProduct_eq K hζ S₀ hS e act U (m*(b⁻¹)^2) ha
      (sourceKPReflectedC1ExteriorPrimes_row_subset K S₀ e m b)
      (sourceKPReflectedC1ExteriorPrimes_order_zero K S₀ e m b)
  have hterm (h : H e) (i : I R M₀) :
      sourceKPPositivePhysicalTranslateWeight K hζ S₀ e R M₀ (mask e act) (h,i) *
        C₁ (one_le_two.trans hT.le) (sourceKPCuspResidualUnitTranslate K hζ m
          (sourceKPReflectedHorizontalFiber K hζ S b
            (sourceKPPositivePhysicalTranslate K hζ S₀ e R M₀ (q₀ a₀) (h,i)) x)) =
      (p * E₀ h) * I₀ i := by
    change (mask e act h * tw e h * sw R M₀ i) *
      C₁ (one_le_two.trans hT.le) (sourceKPCuspResidualUnitTranslate K hζ m
        (sourceKPReflectedHorizontalFiber K hζ S b
          (sourceKPFiniteAdeleUpperLift K hζ (tu e h) *
            sourceKPRetainedSeedTranslate K hζ S R M₀ (q₀ a₀) i) x)) = _
    rw [sourceKPReflectedC1_pointwise K hζ S₀ hS hT m f d e h x R M₀ i a₀]
    dsimp only [p, E₀, I₀, U]
    exact weighted_term_factor (mask e act h * tw e h) (sw R M₀ i) (weyl b x * phase e m b)
      (C₁ (one_le_two.trans hT.le) (L (word m x R M₀ i a₀)).2)
      (∏ P ∈ U, sourceReflectionSignedExteriorWeylValue K S₀ hζ hS P (m*(b⁻¹)^2) (tu e h P.val))
  calc
    _ = ∑ h : H e, ∑ i : I R M₀, (p * E₀ h) * I₀ i := by
      unfold sourceKPReflectedC1ActiveCoefficient
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro i _
      exact hterm h i
    _ = (p * ∑ h, E₀ h) * ∑ i, I₀ i := factor_two_finite_sums p E₀ I₀
    _ = _ := by rw [hsum]; rfl

theorem sourceKPReflectedC1RetainedSum_tensor (hs : 0 < (1 / 6 : ℂ).re)
    {T : ℝ} (hT : 2 < T) (m : Kˣ) (x : SWholeUnits K S) (R M₀ : S → ℕ) (a₀ : A) :
    sourceKPReflectedC1RetainedSum K hζ S₀ hT m x R M₀ a₀ =
      ∑ i : I R M₀, sw R M₀ i *
        ∑ k : SourceKPAdelicOutgoingRetainedJacquetLabel K hζ hs S,
          C₁ (one_le_two.trans hT.le) (L (fun P =>
            sourceKPAdelicOutgoingRetainedJacquetBasisLift K hζ P.val hs (k P))).2 *
          ∏ P : S, sourceKPAdelicOutgoingRetainedJacquetBasisCoordinate K hζ P.val hs (k P)
            (sourceKPAdelicOutgoingRetainedJacquetVector K hζ P.val hs (word m x R M₀ i a₀ P)) := by
  unfold sourceKPReflectedC1RetainedSum
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (sw R M₀ i * ·)
  have hb (P : S) : sourceKPAdelicLocalBase K hζ P.val (1, (1 : Gf)) = 1 := by
    change sourceKPAdelicLocalBase K hζ P.val 1 = 1
    exact map_one _
  simpa only [sourceKPAdelicOutgoingRetainedResidualCoefficient, one_mul] using
    sourceKPAdelicOutgoingRetainedResidualCoefficient_tensor K hζ S hs hT 1 hb (word m x R M₀ i a₀)

end
end ArtinMatthews
