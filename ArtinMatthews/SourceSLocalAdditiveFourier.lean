module

public import ArtinMatthews.SourceNumberFieldArchProbe
public import ArtinMatthews.StandardFiniteAnnularTensor


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory StandardAdelic
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

/-- Additive S-local coordinates, with every complex and every retained finite place. -/
abbrev SLocalAdditiveSpace := (CPlaces → ℂ) × SFiniteSpace K S

/-- The exact product of trace and finite self-dual additive measures. -/
def sourceSLocalAdditiveMeasure : Measure (SLocalAdditiveSpace K S) :=
  (sourceComplexProductMeasure CPlaces).prod (sourceFiniteSelfDualMeasure K S)

/-- The original tensor test on the full additive product. -/
def sourceSLocalAdditiveProbe (x : SLocalAdditiveSpace K S) : ℂ :=
  sourceComplexProductTest x.1 * sourceFiniteUnitTest K S x.2

variable [IsTotallyComplex K]

/-- The standard character in the complex coordinates and the retained finite completions. -/
def sourceSLocalAdditiveCharacter : AddChar (SLocalAdditiveSpace K S) ℂ where
  toFun x := archCharacter K (sourceComplexPlaceAdeleEquiv K x.1) *
    ∏ p : S, localFiniteCharacter K p.val (x.2 p)
  map_zero_eq_one' := by
    change archCharacter K (sourceComplexPlaceAdeleEquiv K 0) *
      (∏ p : S, localFiniteCharacter K p.val 0) = 1
    simp only [map_zero, AddChar.map_zero_eq_one, Finset.prod_const_one, mul_one]
  map_add_eq_mul' x y := by
    change archCharacter K (sourceComplexPlaceAdeleEquiv K (x.1 + y.1)) *
      (∏ p : S, localFiniteCharacter K p.val (x.2 p + y.2 p)) =
        (archCharacter K (sourceComplexPlaceAdeleEquiv K x.1) *
          ∏ p : S, localFiniteCharacter K p.val (x.2 p)) *
        (archCharacter K (sourceComplexPlaceAdeleEquiv K y.1) *
          ∏ p : S, localFiniteCharacter K p.val (y.2 p))
    simp only [map_add, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]
    ac_rfl

theorem sourceSLocalAdditiveCharacter_unitary (x : SLocalAdditiveSpace K S) :
    ‖sourceSLocalAdditiveCharacter K S x‖ = 1 := by
  change ‖archCharacter K (sourceComplexPlaceAdeleEquiv K x.1) *
    ∏ p : S, localFiniteCharacter K p.val (x.2 p)‖ = 1
  simp only [norm_mul, norm_prod, archCharacter_unitary, localFiniteCharacter_unitary,
    Finset.prod_const_one, mul_one]

def sourceSLocalAdditiveFourier (F : SLocalAdditiveSpace K S → ℂ)
    (y : SLocalAdditiveSpace K S) : ℂ :=
  ∫ x, sourceSLocalAdditiveCharacter K S (-(x * y)) * F x ∂sourceSLocalAdditiveMeasure K S

theorem sourceSLocalAdditiveFourier_prod (f : (CPlaces → ℂ) → ℂ)
    (g : SFiniteSpace K S → ℂ) (y : SLocalAdditiveSpace K S) :
    sourceSLocalAdditiveFourier K S (fun x => f x.1 * g x.2) y =
      sourceNumberFieldComplexFourier K f y.1 * sourceFiniteLocalFourier K S g y.2 := by
  let I (a : CPlaces → ℂ) := archCharacter K
    (-(sourceComplexPlaceAdele K a * sourceComplexPlaceAdele K y.1)) * f a
  let J (a : SFiniteSpace K S) := g a *
    ∏ p : S, localFiniteCharacter K p.val (-(y.2 p * a p))
  let (p : S) : (sourceLocalSelfDual K p.val).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K p.val
  have : SigmaFinite (sourceComplexProductMeasure CPlaces) := by
    unfold sourceComplexProductMeasure
    infer_instance
  have : SigmaFinite (sourceFiniteSelfDualMeasure K S) := by
    unfold sourceFiniteSelfDualMeasure
    infer_instance
  have h (x : SLocalAdditiveSpace K S) :
      sourceSLocalAdditiveCharacter K S (-(x * y)) * (f x.1 * g x.2) = I x.1 * J x.2 := by
    change archCharacter K (sourceComplexPlaceAdeleEquiv K (-(x.1 * y.1))) *
        (∏ p : S, localFiniteCharacter K p.val (-(x.2 p * y.2 p))) *
        (f x.1 * g x.2) = _
    rw [map_neg, map_mul]
    have hp : (∏ p : S, localFiniteCharacter K p.val (-(x.2 p * y.2 p))) =
        ∏ p : S, localFiniteCharacter K p.val (-(y.2 p * x.2 p)) :=
      Finset.prod_congr rfl fun p _ => by rw [mul_comm (x.2 p) (y.2 p)]
    rw [hp]
    dsimp only [I, J]
    change archCharacter K (-(sourceComplexPlaceAdele K x.1 * sourceComplexPlaceAdele K y.1)) *
        (∏ p : S, localFiniteCharacter K p.val (-(y.2 p * x.2 p))) *
        (f x.1 * g x.2) = _
    ac_rfl
  unfold sourceSLocalAdditiveFourier sourceSLocalAdditiveMeasure
  simp_rw [h]
  exact integral_prod_mul I J

/-- The full Fourier integral factors into the original local transforms. -/
theorem sourceSLocalAdditiveProbe_fourier_tensor (y : SLocalAdditiveSpace K S) :
    sourceSLocalAdditiveFourier K S (sourceSLocalAdditiveProbe K S) y =
      (∏ w : CPlaces, sourceComplexTraceFourier sourceAnnularSchwartzTest (y.1 w)) *
        ∏ p : S, sourceLocalFourier K p.val (sourceLocalUnitTest K p.val) (y.2 p) := by
  unfold sourceSLocalAdditiveProbe
  rw [sourceSLocalAdditiveFourier_prod,
    sourceNumberFieldComplexFourier_eq, sourceComplexProductTest_fourier_tensor]
  unfold sourceFiniteUnitTest
  rw [sourceFiniteLocalFourier_tensor]

theorem sourceSLocalAdditiveProbe_fourier_zero :
    sourceSLocalAdditiveFourier K S (sourceSLocalAdditiveProbe K S) 0 = 0 := by
  unfold sourceSLocalAdditiveProbe
  rw [sourceSLocalAdditiveFourier_prod]
  change sourceNumberFieldComplexFourier K sourceComplexProductTest 0 * _ = _
  rw [sourceNumberFieldComplexFourier_test_zero, zero_mul]

theorem sourceSLocalAdditiveProbe_integral_zero :
    (∫ x, sourceSLocalAdditiveProbe K S x ∂sourceSLocalAdditiveMeasure K S) = 0 := by
  simpa only [sourceSLocalAdditiveFourier, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
    using sourceSLocalAdditiveProbe_fourier_zero K S

end
end ArtinMatthews.SourcePhysical
