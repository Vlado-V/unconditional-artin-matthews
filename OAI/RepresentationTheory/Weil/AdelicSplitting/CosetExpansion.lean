module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.CosetTestFamilies
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.ENatToNat
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteTestSupport


set_option backward.privateInPublic true
@[expose] public section

/-! # Coset Expansion -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! Every restricted test family's actual adelic values and convergent
theta sum expand into finitely many compact open finite cosets. -/

open scoped Classical _root_.NumberField

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.coset_value_expansion (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ∃ M : ℕ, ∃ hM : 0 < M,
      ∃ s : Finset (FiniteCosets.Construction.FinitePositionQuotient (ι := Fin N) (M : F) (by exact_mod_cast hM.ne')),
        ∀ x : Fin N → ArchimedeanAdeles.Construction.Adeles F,
          f.value F N x = ∑ c ∈ s,
            f.finiteValue F N (FiniteCosets.Construction.finiteRationalPosition (FiniteCosets.Construction.finitePositionQuotientRep (M : F) (by exact_mod_cast hM.ne') c)) *
              (f.replaceFiniteByCoset F N (M : F) (by exact_mod_cast hM.ne')
                (FiniteCosets.Construction.finiteRationalPosition (FiniteCosets.Construction.finitePositionQuotientRep (M : F) (by exact_mod_cast hM.ne') c))).value F N x := by
  obtain ⟨M, hM, hp⟩ := FiniteLattices.Construction.finite_locallyConstant_lattice_period (f.finiteValue F N)
    (f.finiteValue_locallyConstant F N) (f.finiteValue_compactSupport F N)
  let hm : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  obtain ⟨s, hs⟩ := FiniteCosets.Construction.finite_function_coset_expansion (f.finiteValue F N)
    (f.finiteValue_compactSupport F N) (M : F) hm hp
  refine ⟨M, hM, s, fun x => ?_⟩
  rw [f.value_factorization F N, hs (fun i => (x i).2), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [RestrictedTestFamilies.Construction.RestrictedTestFamily.value_factorization, RestrictedTestFamilies.Construction.RestrictedTestFamily.replaceFiniteByCoset_finiteValue]
  change (∏ v : NumberField.InfinitePlace F, (f (.inl v)).val (fun i => (x i).1 v)) * (_ * _) =
    _ * ((∏ v : NumberField.InfinitePlace F, (f (.inl v)).val (fun i => (x i).1 v)) * _)
  ring

theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_coset_expansion (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    ∃ M : ℕ, ∃ hM : 0 < M,
      ∃ s : Finset (FiniteCosets.Construction.FinitePositionQuotient (ι := Fin N) (M : F) (by exact_mod_cast hM.ne')),
        f.theta F N = ∑ c ∈ s,
          f.finiteValue F N (FiniteCosets.Construction.finiteRationalPosition (FiniteCosets.Construction.finitePositionQuotientRep (M : F) (by exact_mod_cast hM.ne') c)) *
            (f.replaceFiniteByCoset F N (M : F) (by exact_mod_cast hM.ne')
              (FiniteCosets.Construction.finiteRationalPosition (FiniteCosets.Construction.finitePositionQuotientRep (M : F) (by exact_mod_cast hM.ne') c))).theta F N := by
  obtain ⟨M, hM, s, hs⟩ := f.coset_value_expansion F N
  refine ⟨M, hM, s, ?_⟩
  change (∑' q : Fin N → F, f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))) = _
  simp_rw [hs]
  rw [Summable.tsum_finsetSum]
  · simp only [tsum_mul_left]
    rfl
  · intro c _
    exact ((f.replaceFiniteByCoset F N (M : F) (by exact_mod_cast hM.ne')
      (FiniteCosets.Construction.finiteRationalPosition (FiniteCosets.Construction.finitePositionQuotientRep (M : F) (by exact_mod_cast hM.ne') c))).theta_summable F N).mul_left _

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
