module

public import ArtinMatthews.StandardLocalUnitTest
public import ArtinMatthews.StandardLocalHaarScaling
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite S tensor test and its literal standard Fourier
transform. The local unit annulus and its two codifferent balls retain
their exact ramified self-dual constants. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem sourceLocalUnitTestFourier_norm (P : HeightOneSpectrum (𝓞 K)) (y : P.adicCompletion K) :
    sourceLocalFourier K P (sourceLocalUnitTest K P) y =
      (Real.rpow (Ideal.absNorm P.asIdeal : ℝ) (-(sourceDifferentExponent K P : ℝ) / 2) : ℂ) *
        (sourceLocalBallIndicator K P (sourceDifferentExponent K P : ℤ) y -
          (Ideal.absNorm P.asIdeal : ℂ)⁻¹ *
            sourceLocalBallIndicator K P ((sourceDifferentExponent K P : ℤ) + 1) y) := by
  let : (sourceLocalSelfDual K P).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  let c := Real.rpow (Ideal.absNorm P.asIdeal : ℝ) (-(sourceDifferentExponent K P : ℝ) / 2)
  have hc : (sourceLocalSelfDual K P).real (sourceLocalBall K P 0) = c :=
    sourceLocalSelfDual_volume_integer K P
  change _ = (c : ℂ) * _
  rw [sourceLocalUnitTestFourier_raw, sourceLocalPrimeBall_volume K P (sourceLocalSelfDual K P),
    hc, Complex.ofReal_div, Complex.ofReal_natCast]
  ring

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

abbrev SFiniteSpace := ∀ v : S, v.val.adicCompletion K

def sourceFiniteSelfDualMeasure : Measure (SFiniteSpace K S) :=
  Measure.pi (fun v : S => sourceLocalSelfDual K v.val)

def sourceFiniteUnitTest (x : SFiniteSpace K S) : ℂ := ∏ v : S, sourceLocalUnitTest K v.val (x v)

def sourceFiniteLocalFourier (f : SFiniteSpace K S → ℂ) (y : SFiniteSpace K S) : ℂ :=
  ∫ x, f x * ∏ v : S, localFiniteCharacter K v.val (-(y v * x v)) ∂sourceFiniteSelfDualMeasure K S

theorem sourceFiniteUnitTest_locallyConstant : IsLocallyConstant (sourceFiniteUnitTest K S) := by
  have h (t : Finset S) : IsLocallyConstant (fun x : SFiniteSpace K S =>
      ∏ v ∈ t, sourceLocalUnitTest K v.val (x v)) := by
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact IsLocallyConstant.one
    | @insert a s ha hs =>
      simp only [Finset.prod_insert ha]
      exact ((sourceLocalUnitTest_locallyConstant K a.val).comp_continuous (continuous_apply a)).mul hs
  exact h Finset.univ

def sourceFiniteUnitAnnulus : Set (SFiniteSpace K S) := Set.univ.pi (fun v : S => sourceLocalUnitAnnulus K v.val)

theorem sourceFiniteUnitAnnulus_isCompact : IsCompact (sourceFiniteUnitAnnulus K S) :=
  isCompact_univ_pi (fun v => sourceLocalUnitAnnulus_isCompact K v.val)

theorem sourceFiniteUnitTest_eq_zero_outside (x : SFiniteSpace K S) (hx : x ∉ sourceFiniteUnitAnnulus K S) :
    sourceFiniteUnitTest K S x = 0 := by
  have he : ¬ ∀ v : S, x v ∈ sourceLocalUnitAnnulus K v.val := fun h => hx (fun v _ => h v)
  obtain ⟨v, hv⟩ := not_forall.mp he
  unfold sourceFiniteUnitTest
  exact Finset.prod_eq_zero (Finset.mem_univ v) (Set.indicator_of_notMem hv _)

theorem sourceFiniteUnitTest_compactSupport : HasCompactSupport (sourceFiniteUnitTest K S) :=
  HasCompactSupport.intro (sourceFiniteUnitAnnulus_isCompact K S) (sourceFiniteUnitTest_eq_zero_outside K S)

theorem sourceFiniteUnitTest_support_away_zero {x : SFiniteSpace K S}
    (hx : x ∈ tsupport (sourceFiniteUnitTest K S)) (v : S) : x v ≠ 0 := by
  have hs : tsupport (sourceFiniteUnitTest K S) ⊆ sourceFiniteUnitAnnulus K S := by
    apply closure_minimal _ (sourceFiniteUnitAnnulus_isCompact K S).isClosed
    intro y hy
    by_contra hn
    exact hy (sourceFiniteUnitTest_eq_zero_outside K S y hn)
  exact sourceLocalUnitAnnulus_ne_zero K v.val ((hs hx) v (Set.mem_univ v))

theorem sourceFiniteLocalFourier_tensor (f : (v : S) → v.val.adicCompletion K → ℂ) (y : SFiniteSpace K S) :
    sourceFiniteLocalFourier K S (fun x => ∏ v : S, f v (x v)) y =
      ∏ v : S, sourceLocalFourier K v.val (f v) (y v) := by
  let (v : S) : (sourceLocalSelfDual K v.val).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K v.val
  unfold sourceFiniteLocalFourier sourceFiniteSelfDualMeasure
  simp_rw [← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (μ := fun v : S => sourceLocalSelfDual K v.val)
    (fun v x => f v x * localFiniteCharacter K v.val (-(y v * x)))

theorem sourceFiniteUnitTest_fourier (y : SFiniteSpace K S) :
    sourceFiniteLocalFourier K S (sourceFiniteUnitTest K S) y =
      ∏ v : S, (Real.rpow (Ideal.absNorm v.val.asIdeal : ℝ) (-(sourceDifferentExponent K v.val : ℝ) / 2) : ℂ) *
        (sourceLocalBallIndicator K v.val (sourceDifferentExponent K v.val : ℤ) (y v) -
          (Ideal.absNorm v.val.asIdeal : ℂ)⁻¹ *
            sourceLocalBallIndicator K v.val ((sourceDifferentExponent K v.val : ℤ) + 1) (y v)) := by
  unfold sourceFiniteUnitTest
  rw [sourceFiniteLocalFourier_tensor]
  exact Finset.prod_congr rfl (fun v _ => sourceLocalUnitTestFourier_norm K v.val (y v))

def sourceFiniteUnitTestChoice (v : S) (b : Fin 2) (x : v.val.adicCompletion K) : ℂ :=
  if b = 0 then sourceLocalBallIndicator K v.val 0 x else -sourceLocalBallIndicator K v.val (-1) x

theorem sourceFiniteUnitTest_sum_choices (x : SFiniteSpace K S) :
    sourceFiniteUnitTest K S x = ∑ b : S → Fin 2, ∏ v : S, sourceFiniteUnitTestChoice K S v (b v) (x v) := by
  have h (v : S) : sourceLocalUnitTest K v.val (x v) =
      ∑ b : Fin 2, sourceFiniteUnitTestChoice K S v b (x v) := by
    rw [sourceLocalUnitTest_eq_diff, Fin.sum_univ_two]
    simp [sourceFiniteUnitTestChoice, sub_eq_add_neg]
  unfold sourceFiniteUnitTest
  simp_rw [h]
  exact Fintype.prod_sum (fun v b => sourceFiniteUnitTestChoice K S v b (x v))

end
end ArtinMatthews.SourcePhysical
