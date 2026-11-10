module

public import ArtinMatthews.SixthExteriorReduction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.SelbergSieve
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


set_option backward.privateInPublic true
@[expose] public section

/-! Actual bounded ideal rows. Each nonzero ideal gets a genuine field
generator outside the constructed class-support set. Multiplication by
the finite S-unit representatives gives rows with exactly the original
ideal's exterior prime exponents and literal ideal norm bound. -/
namespace ArtinMatthews
open IsDedekindDomain FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def exteriorIdealGenerator (I : Ideal (𝓞 K)) (hI : I ≠ 0) : Kˣ :=
  (exists_principal_generator_outside_class_support
    (FractionalIdeal.mk0 K ⟨I,mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩)).choose

theorem exteriorIdealGenerator_valuation (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ exteriorPrincipalizingPrimes K) :
    exteriorPrincipalValuation p (exteriorIdealGenerator I hI)=
      FractionalIdeal.count K p (I:FractionalIdeal (𝓞 K)⁰ K) :=
  (exists_principal_generator_outside_class_support
    (FractionalIdeal.mk0 K ⟨I,mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩)).choose_spec p hp

def exteriorBoundedIdealRows (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) N).toFinset.filter fun I =>
    I ≠ 0 ∧ (∀ p ∈ S, FractionalIdeal.count K p (I:FractionalIdeal (𝓞 K)⁰ K)=0) ∧
      ∀ p : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K p (I:FractionalIdeal (𝓞 K)⁰ K)<6

theorem mem_exteriorBoundedIdealRows (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ)
    (I : Ideal (𝓞 K)) :
    I ∈ exteriorBoundedIdealRows S N ↔ I.absNorm ≤ N ∧ I ≠ 0 ∧
      (∀ p ∈ S, FractionalIdeal.count K p (I:FractionalIdeal (𝓞 K)⁰ K)=0) ∧
      ∀ p : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K p (I:FractionalIdeal (𝓞 K)⁰ K)<6 := by
  simp only [exteriorBoundedIdealRows,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]

def exteriorIdealRow (S : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K))
    (hI : I ≠ 0) (r : exteriorUnitSubgroup S) : Kˣ := exteriorIdealGenerator I hI * (r:Kˣ)

theorem exteriorIdealRow_valuation (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (r : exteriorUnitSubgroup S) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    exteriorPrincipalValuation p (exteriorIdealRow S I hI r)=
      FractionalIdeal.count K p (I:FractionalIdeal (𝓞 K)⁰ K) := by
  rw [exteriorIdealRow,exteriorPrincipalValuation_mul,
    exteriorIdealGenerator_valuation I hI p (fun h => hp (hS h)),r.2 p hp,add_zero]

theorem exteriorIdealRow_reduced (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ)
    (I : Ideal (𝓞 K)) (hI : I ∈ exteriorBoundedIdealRows S N) (r : exteriorUnitSubgroup S) :
    ExteriorSixthReduced S (exteriorIdealRow S I
      ((mem_exteriorBoundedIdealRows S N I).mp hI).2.1 r) := by
  intro p hp
  rw [exteriorIdealRow_valuation S hS I _ r p hp]
  exact ⟨FractionalIdeal.count_coe_nonneg K p I,
    ((mem_exteriorBoundedIdealRows S N I).mp hI).2.2.2 p⟩

/-- A sixth-power ratio of two bounded ideal rows forces equality of
their actual ideals. This is proved from all exterior prime exponents. -/
theorem exteriorIdealRow_ideal_eq_of_sixthPower
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) (I J : Ideal (𝓞 K)) (hI : I ∈ exteriorBoundedIdealRows S N)
    (hJ : J ∈ exteriorBoundedIdealRows S N) (r s : exteriorUnitSubgroup S)
    (t : Kˣ)
    (hpow : exteriorIdealRow S I ((mem_exteriorBoundedIdealRows S N I).mp hI).2.1 r /
      exteriorIdealRow S J ((mem_exteriorBoundedIdealRows S N J).mp hJ).2.1 s=t^6) : I=J := by
  have hIc := (mem_exteriorBoundedIdealRows S N I).mp hI
  have hJc := (mem_exteriorBoundedIdealRows S N J).mp hJ
  have hval : ∀ p : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K p (I:FractionalIdeal (𝓞 K)⁰ K)=
        FractionalIdeal.count K p (J:FractionalIdeal (𝓞 K)⁰ K) := by
    intro p
    by_cases hp : p ∈ S
    · rw [hIc.2.2.1 p hp,hJc.2.2.1 p hp]
    · have he := (exteriorSixthReduced_ratio_root S _ _ t
        (exteriorIdealRow_reduced S hS N I hI r)
        (exteriorIdealRow_reduced S hS N J hJ s) hpow).1 p hp
      rwa [exteriorIdealRow_valuation S hS I _ r p hp,
        exteriorIdealRow_valuation S hS J _ s p hp] at he
  have he : (I:FractionalIdeal (𝓞 K)⁰ K)=(J:FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      (K := K) (FractionalIdeal.coeIdeal_ne_zero.mpr hIc.2.1),
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      (K := K) (FractionalIdeal.coeIdeal_ne_zero.mpr hJc.2.1)]
    exact finprod_congr fun p => by rw [hval p]
  exact FractionalIdeal.coeIdeal_injective he

end
end ArtinMatthews
