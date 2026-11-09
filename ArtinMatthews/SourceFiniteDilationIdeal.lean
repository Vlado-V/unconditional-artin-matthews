module

public import ArtinMatthews.SourceFiniteBallIdeal
public import ArtinMatthews.StandardFiniteAnnularTensor
public import ArtinMatthews.StandardLocalBallDilation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite S annular test after an arbitrary local dilation
is a finite signed sum of genuine fractional-ideal membership tests on
the original S-integers. Every local radius and sign is literal. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain FractionalIdeal StandardAdelic
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def sourceFiniteChoiceRadius (b : Fin 2) : ℤ := if b = 0 then 0 else -1

def sourceFiniteChoiceSign (b : Fin 2) : ℂ := if b = 0 then 1 else -1

theorem sourceFiniteUnitTestChoice_eq_signed_ball (v : S) (b : Fin 2) (x : v.val.adicCompletion K) :
    sourceFiniteUnitTestChoice K S v b x = sourceFiniteChoiceSign b *
      sourceLocalBallIndicator K v.val (sourceFiniteChoiceRadius b) x := by
  by_cases hb : b = 0 <;> simp [sourceFiniteUnitTestChoice, sourceFiniteChoiceSign, sourceFiniteChoiceRadius, hb]

abbrev SFiniteUnits := ∀ v : S, (v.val.adicCompletion K)ˣ

def sourceFiniteDilationPoint (t : SFiniteUnits K S) (x : K) : SFiniteSpace K S :=
  fun v => algebraMap K (v.val.adicCompletion K) x / (t v : v.val.adicCompletion K)

def sourceFiniteDilationExponent (t : SFiniteUnits K S) (b : S → Fin 2) (v : S) : ℤ :=
  -sourceFiniteChoiceRadius (b v) - WithZero.log (sourceLocalValuation K v.val (t v : v.val.adicCompletion K))

def sourceFiniteDilationIdeal (t : SFiniteUnits K S) (b : S → Fin 2) : FractionalIdeal (𝓞 K)⁰ K :=
  sourceFiniteBallIdeal K S (sourceFiniteDilationExponent K S t b)

theorem sourceFiniteDilationIdeal_ne_zero (t : SFiniteUnits K S) (b : S → Fin 2) :
    sourceFiniteDilationIdeal K S t b ≠ 0 := sourceFiniteBallIdeal_ne_zero K S _

theorem sourceFiniteDilationIdeal_mem_iff (t : SFiniteUnits K S) (b : S → Fin 2) (x : sIntegerRing K S) :
    (x : K) ∈ sourceFiniteDilationIdeal K S t b ↔
      ∀ v : S, sourceFiniteDilationPoint K S t (x : K) v ∈
        sourceLocalBall K v.val (sourceFiniteChoiceRadius (b v)) := by
  unfold sourceFiniteDilationIdeal
  rw [sourceFiniteBallIdeal_sInteger_mem_iff]
  apply forall_congr'
  intro v
  unfold sourceFiniteDilationPoint
  rw [sourceLocalBall_div_mem]
  have he : -sourceFiniteDilationExponent K S t b v = sourceFiniteChoiceRadius (b v) +
      WithZero.log (sourceLocalValuation K v.val (t v : v.val.adicCompletion K)) := by
    unfold sourceFiniteDilationExponent
    ring
  rw [he]

theorem sourceFiniteDilationPattern_eq_ideal (t : SFiniteUnits K S) (b : S → Fin 2) (x : sIntegerRing K S) :
    (∏ v : S, sourceFiniteUnitTestChoice K S v (b v) (sourceFiniteDilationPoint K S t (x : K) v)) =
      if (x : K) ∈ sourceFiniteDilationIdeal K S t b then ∏ v : S, sourceFiniteChoiceSign (b v) else 0 := by
  by_cases hx : (x : K) ∈ sourceFiniteDilationIdeal K S t b
  · rw [ite_eq_left hx]
    apply Finset.prod_congr rfl
    intro v _
    have h := (sourceFiniteDilationIdeal_mem_iff K S t b x).mp hx v
    rw [sourceFiniteUnitTestChoice_eq_signed_ball, sourceLocalBallIndicator, Set.indicator_of_mem h, mul_one]
  · rw [ite_eq_right hx]
    have hn : ¬ ∀ v : S, sourceFiniteDilationPoint K S t (x : K) v ∈
        sourceLocalBall K v.val (sourceFiniteChoiceRadius (b v)) :=
      fun h => hx ((sourceFiniteDilationIdeal_mem_iff K S t b x).mpr h)
    obtain ⟨v, hv⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    rw [sourceFiniteUnitTestChoice_eq_signed_ball, sourceLocalBallIndicator, Set.indicator_of_notMem hv, mul_zero]

theorem sourceFiniteUnitTest_dilation_ideal_expansion (t : SFiniteUnits K S) (x : sIntegerRing K S) :
    sourceFiniteUnitTest K S (sourceFiniteDilationPoint K S t (x : K)) =
      ∑ b : S → Fin 2, if (x : K) ∈ sourceFiniteDilationIdeal K S t b then
        ∏ v : S, sourceFiniteChoiceSign (b v) else 0 := by
  rw [sourceFiniteUnitTest_sum_choices]
  apply Finset.sum_congr rfl
  intro b _
  exact sourceFiniteDilationPattern_eq_ideal K S t b x

end
end ArtinMatthews.SourcePhysical
