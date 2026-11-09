module

public import ArtinMatthews.SourceReflectionDirichlet


set_option backward.privateInPublic true
@[expose] public section

/-! Decompose the integral numerator of a reflected frequency. Outside
the frozen primes, divide the valuation by three and retain its
squarefree remainder. The two parts can have common primes. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Prime" => SourceExteriorPrime F S₀
local notation "E" => SourcePrimeExponents F S₀

abbrev SourceReflectionNumerator (d : E) :=
  {e : E // (∀ P, e P % 3 ≤ 1) ∧ ∀ P ∈ d.support, e P = 0}

abbrev SourceReflectionSupportedTermIndex (f : Finset Prime) (d : E) :=
  {i : SourceReflectionTermIndex F S₀ f //
    (∀ P ∈ f, i.1.val P % 3 ≤ 1 ∧ i.2.1 P = 0 ∧ i.2.2.val P = 0) ∧
      ∀ P ∈ d.support, i.1.val P = 0 ∧ i.2.1 P = 0 ∧ i.2.2.val P = 0}

def sourceReflectionSplitNumerator (f : Finset Prime) (d : E)
    (e : SourceReflectionNumerator F S₀ d) : SourceReflectionSupportedTermIndex F S₀ f d := by
  let a := e.val.filter (· ∈ f)
  let r := e.val.filter (· ∉ f)
  let n := r.mapRange (· / 3) (by decide)
  let c := r.mapRange (· % 3) (by decide)
  have ha : a.support ⊆ f := by
    intro P hP
    by_contra h
    exact (Finsupp.mem_support_iff.mp hP) (by simp [a, Finsupp.filter_apply, h])
  have hc : sourceReflectionIsSquarefree c := by
    intro P
    by_cases hP : P ∈ f
    · simp [c, r, Finsupp.filter_apply, hP]
    · simpa [c, r, Finsupp.filter_apply, hP] using e.property.1 P
  refine ⟨(⟨a,ha⟩, n, ⟨c,hc⟩), ?_, ?_⟩
  · intro P hP
    simpa [a, n, c, r, Finsupp.filter_apply, hP] using e.property.1 P
  · intro P hP
    simp [a, n, c, r, Finsupp.filter_apply, e.property.2 P hP]

def sourceReflectionCombineNumerator (f : Finset Prime) (d : E)
    (i : SourceReflectionSupportedTermIndex F S₀ f d) : SourceReflectionNumerator F S₀ d := by
  refine ⟨i.val.1.val + i.val.2.2.val + 3 • i.val.2.1, ?_, ?_⟩
  · intro P
    simp only [Finsupp.add_apply, Finsupp.nsmul_apply, nsmul_eq_mul]
    by_cases hP : P ∈ f
    · obtain ⟨hm,hn,hc⟩ := i.property.1 P hP
      simpa [hn,hc] using hm
    · have ha : i.val.1.val P = 0 := Finsupp.notMem_support_iff.mp (fun h => hP (i.val.1.property h))
      have hc := i.val.2.2.property P
      omega
  · intro P hP
    obtain ⟨ha,hn,hc⟩ := i.property.2 P hP
    simp [Finsupp.add_apply, Finsupp.nsmul_apply, ha, hn, hc]

theorem sourceReflectionCombineNumerator_split (f : Finset Prime) (d : E)
    (e : SourceReflectionNumerator F S₀ d) :
    sourceReflectionCombineNumerator F S₀ f d (sourceReflectionSplitNumerator F S₀ f d e) = e := by
  apply Subtype.ext
  ext P
  simp only [sourceReflectionCombineNumerator, sourceReflectionSplitNumerator, Finsupp.add_apply,
    Finsupp.nsmul_apply, nsmul_eq_mul, Finsupp.mapRange_apply, Finsupp.filter_apply]
  by_cases hP : P ∈ f
  · simp [hP]
  · simp only [hP, not_false_eq_true, if_false, if_true, zero_add]
    omega

theorem sourceReflectionSplitNumerator_combine (f : Finset Prime) (d : E)
    (i : SourceReflectionSupportedTermIndex F S₀ f d) :
    sourceReflectionSplitNumerator F S₀ f d (sourceReflectionCombineNumerator F S₀ f d i) = i := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    ext P
    simp only [sourceReflectionCombineNumerator, sourceReflectionSplitNumerator, Finsupp.add_apply,
      Finsupp.nsmul_apply, nsmul_eq_mul, Finsupp.filter_apply]
    by_cases hP : P ∈ f
    · obtain ⟨_,hn,hc⟩ := i.property.1 P hP
      simp [hP, hn, hc]
    · have ha : i.val.1.val P = 0 := Finsupp.notMem_support_iff.mp (fun h => hP (i.val.1.property h))
      simp [hP, ha]
  · apply Prod.ext
    · ext P
      simp only [sourceReflectionCombineNumerator, sourceReflectionSplitNumerator, Finsupp.add_apply,
        Finsupp.nsmul_apply, nsmul_eq_mul, Finsupp.mapRange_apply, Finsupp.filter_apply]
      by_cases hP : P ∈ f
      · simp [hP, (i.property.1 P hP).2.1]
      · have ha : i.val.1.val P = 0 := Finsupp.notMem_support_iff.mp (fun h => hP (i.val.1.property h))
        have hc := i.val.2.2.property P
        simp only [hP, not_false_eq_true, if_true, ha, zero_add]
        omega
    · apply Subtype.ext
      ext P
      simp only [sourceReflectionCombineNumerator, sourceReflectionSplitNumerator, Finsupp.add_apply,
        Finsupp.nsmul_apply, nsmul_eq_mul, Finsupp.mapRange_apply, Finsupp.filter_apply]
      by_cases hP : P ∈ f
      · simp [hP, (i.property.1 P hP).2.2]
      · have ha : i.val.1.val P = 0 := Finsupp.notMem_support_iff.mp (fun h => hP (i.val.1.property h))
        have hc := i.val.2.2.property P
        simp only [hP, not_false_eq_true, if_true, ha, zero_add]
        omega

def sourceReflectionNumeratorEquiv (f : Finset Prime) (d : E) :
    SourceReflectionNumerator F S₀ d ≃ SourceReflectionSupportedTermIndex F S₀ f d where
  toFun := sourceReflectionSplitNumerator F S₀ f d
  invFun := sourceReflectionCombineNumerator F S₀ f d
  left_inv := sourceReflectionCombineNumerator_split F S₀ f d
  right_inv := sourceReflectionSplitNumerator_combine F S₀ f d

end
end ArtinMatthews.SourceEulerAssembly
