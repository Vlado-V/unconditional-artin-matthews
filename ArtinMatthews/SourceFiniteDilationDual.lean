module

public import ArtinMatthews.SourceFiniteDilationIdeal
public import ArtinMatthews.SourceFiniteBallIdealVolume


set_option backward.privateInPublic true
@[expose] public section

/-! The finite Poisson side of every signed annular pattern, with the
actual dilation modulus and the exact finite Fourier transform. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def sourceFiniteDilationNorm (t : SFiniteUnits K S) : ℝ :=
  ∏ v : S, ‖(t v : v.val.adicCompletion K)‖

def sourceFiniteDilationMul (t : SFiniteUnits K S) (y : SFiniteSpace K S) : SFiniteSpace K S :=
  fun v => (t v : v.val.adicCompletion K) * y v

def sourceFiniteDilationDualRadius (v : S) (t : (v.val.adicCompletion K)ˣ) (b : Fin 2) : ℤ :=
  (sourceDifferentExponent K v.val : ℤ) - sourceFiniteChoiceRadius b -
    WithZero.log (sourceLocalValuation K v.val (t : v.val.adicCompletion K))

theorem sourceFiniteDilationDualRadius_eq (t : SFiniteUnits K S) (b : S → Fin 2) (v : S) :
    sourceFiniteDilationDualRadius K S v (t v) (b v) =
      (sourceDifferentExponent K v.val : ℤ) + sourceFiniteDilationExponent K S t b v := by
  unfold sourceFiniteDilationDualRadius sourceFiniteDilationExponent
  ring

theorem sourceFiniteDilationDual_mem_iff (v : S) (t : (v.val.adicCompletion K)ˣ) (b : Fin 2)
    (y : v.val.adicCompletion K) :
    y ∈ sourceLocalBall K v.val (sourceFiniteDilationDualRadius K S v t b) ↔
      (t : v.val.adicCompletion K) * y ∈ sourceLocalBall K v.val
        ((sourceDifferentExponent K v.val : ℤ) - sourceFiniteChoiceRadius b) := by
  have h := sourceLocalBall_div_mem K v.val (sourceFiniteDilationDualRadius K S v t b) t
    ((t : v.val.adicCompletion K) * y)
  rw [mul_div_cancel_left₀ _ t.ne_zero] at h
  have he : sourceFiniteDilationDualRadius K S v t b +
      WithZero.log (sourceLocalValuation K v.val (t : v.val.adicCompletion K)) =
        (sourceDifferentExponent K v.val : ℤ) - sourceFiniteChoiceRadius b := by
    unfold sourceFiniteDilationDualRadius
    ring
  rw [he] at h
  exact h

theorem sourceFiniteDilationDual_indicator (v : S) (t : (v.val.adicCompletion K)ˣ) (b : Fin 2)
    (y : v.val.adicCompletion K) :
    sourceLocalBallIndicator K v.val (sourceFiniteDilationDualRadius K S v t b) y =
      sourceLocalBallIndicator K v.val ((sourceDifferentExponent K v.val : ℤ) -
        sourceFiniteChoiceRadius b) ((t : v.val.adicCompletion K) * y) := by
  unfold sourceLocalBallIndicator
  by_cases hy : y ∈ sourceLocalBall K v.val (sourceFiniteDilationDualRadius K S v t b)
  · simp only [Set.indicator_of_mem hy, Set.indicator_of_mem
      ((sourceFiniteDilationDual_mem_iff K S v t b y).mp hy)]
  · simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem
      (fun h => hy ((sourceFiniteDilationDual_mem_iff K S v t b y).mpr h))]

def sourceFiniteDilationDualLocal (v : S) (t : (v.val.adicCompletion K)ˣ) (b : Fin 2)
    (y : v.val.adicCompletion K) : ℂ :=
  sourceFiniteChoiceSign b *
    ((sourceLocalSelfDual K v.val).real (sourceLocalBall K v.val
      (sourceFiniteChoiceRadius b + WithZero.log (sourceLocalValuation K v.val (t : v.val.adicCompletion K)))) : ℂ) *
    sourceLocalBallIndicator K v.val (sourceFiniteDilationDualRadius K S v t b) y

theorem sourceFiniteDilationDualLocal_sum (v : S) (t : (v.val.adicCompletion K)ˣ)
    (y : v.val.adicCompletion K) :
    (∑ b : Fin 2, sourceFiniteDilationDualLocal K S v t b y) =
      (‖(t : v.val.adicCompletion K)‖ : ℂ) *
        sourceLocalFourier K v.val (sourceLocalUnitTest K v.val) ((t : v.val.adicCompletion K) * y) := by
  let : (sourceLocalSelfDual K v.val).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K v.val
  have hvol (b : Fin 2) :
      (sourceLocalSelfDual K v.val).real (sourceLocalBall K v.val (sourceFiniteChoiceRadius b +
        WithZero.log (sourceLocalValuation K v.val (t : v.val.adicCompletion K)))) =
      ‖(t : v.val.adicCompletion K)‖ *
        (sourceLocalSelfDual K v.val).real (sourceLocalBall K v.val (sourceFiniteChoiceRadius b)) :=
    sourceLocalBall_dilation_volume K v.val (sourceLocalSelfDual K v.val) (sourceFiniteChoiceRadius b) t
  unfold sourceFiniteDilationDualLocal
  simp_rw [hvol, sourceFiniteDilationDual_indicator K S v t,
    Complex.ofReal_mul]
  rw [Fin.sum_univ_two, sourceLocalUnitTestFourier_raw]
  simp [sourceFiniteChoiceRadius, sourceFiniteChoiceSign]
  ring

def sourceFiniteDilationDualWeight (t : SFiniteUnits K S) (b : S → Fin 2)
    (y : SFiniteSpace K S) : ℂ :=
  if ∀ v : S, y v ∈ sourceLocalBall K v.val
      ((sourceDifferentExponent K v.val : ℤ) + sourceFiniteDilationExponent K S t b v)
  then (∏ v : S, sourceFiniteChoiceSign (b v)) *
    ((∏ v : S, (sourceLocalSelfDual K v.val).real
      (sourceLocalBall K v.val (-(sourceFiniteDilationExponent K S t b v))) : ℝ) : ℂ)
  else 0

theorem sourceFiniteDilationDualWeight_eq_prod (t : SFiniteUnits K S) (b : S → Fin 2)
    (y : SFiniteSpace K S) :
    sourceFiniteDilationDualWeight K S t b y = ∏ v : S, sourceFiniteDilationDualLocal K S v (t v) (b v) (y v) := by
  have hvol (v : S) : -(sourceFiniteDilationExponent K S t b v) =
      sourceFiniteChoiceRadius (b v) +
        WithZero.log (sourceLocalValuation K v.val (t v : v.val.adicCompletion K)) := by
    unfold sourceFiniteDilationExponent
    ring
  unfold sourceFiniteDilationDualWeight
  split
  · rename_i h
    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v _
    rw [sourceFiniteDilationDualLocal, sourceFiniteDilationDualRadius_eq K S t b v,
      sourceLocalBallIndicator, Set.indicator_of_mem (h v), mul_one, hvol]
  · rename_i h
    obtain ⟨v, hv⟩ := not_forall.mp h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    rw [sourceFiniteDilationDualLocal, sourceFiniteDilationDualRadius_eq K S t b v,
      sourceLocalBallIndicator, Set.indicator_of_notMem hv, mul_zero]

theorem sourceFiniteDilationDualWeight_sum (t : SFiniteUnits K S) (y : SFiniteSpace K S) :
    (∑ b : S → Fin 2, sourceFiniteDilationDualWeight K S t b y) =
      (sourceFiniteDilationNorm K S t : ℂ) *
        sourceFiniteLocalFourier K S (sourceFiniteUnitTest K S) (sourceFiniteDilationMul K S t y) := by
  simp_rw [sourceFiniteDilationDualWeight_eq_prod]
  rw [← Fintype.prod_sum (fun v b => sourceFiniteDilationDualLocal K S v (t v) b (y v))]
  simp_rw [sourceFiniteDilationDualLocal_sum]
  unfold sourceFiniteDilationNorm sourceFiniteUnitTest
  rw [Finset.prod_mul_distrib, Complex.ofReal_prod, sourceFiniteLocalFourier_tensor]
  rfl

end
end ArtinMatthews.SourcePhysical
