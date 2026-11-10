module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.FiniteQuadratic
public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
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
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.Local.FiniteQuadraticPieces


set_option backward.privateInPublic true
@[expose] public section

/-! # Finite Quadratic Phase -/

namespace OAI.RepresentationTheory.Weil.Local

noncomputable section

/-! The eighth-root phase theorem for every nonzero finite quadratic Gauss sum. -/

open scoped Classical

universe u

theorem FiniteQuadratic.Construction.QuadraticCharacter.phase_gauss_eighth {A : Type u} [AddCommGroup A] [Fintype A]
    (q : FiniteQuadratic.Construction.QuadraticCharacter A) (hq : q.gauss ≠ 0) : FunctionsMetaplectic.Construction.phase q.gauss ^ 8 = 1 := by
  induction hcard : Fintype.card A using Nat.strong_induction_on generalizing A with
  | h n ih =>
    rcases subsingleton_or_nontrivial A with hs | hn
    · let : Subsingleton A := hs
      have hv : ∀ x : A, q x = 1 := fun x => (Subsingleton.elim x 0) ▸ q.map_zero
      simp [FiniteQuadratic.Construction.QuadraticCharacter.gauss, hv, FunctionsMetaplectic.Construction.phase]
    · let : Nontrivial A := hn
      by_cases hani : ∀ x, q x = 1 → x = 0
      · obtain ⟨H, hH, hnd, hphase⟩ := q.anisotropic_has_phase_piece hq hani
        let : Nontrivial H := hH
        have hlt : Fintype.card (q.orthogonal H) < n := by
          rw [← hcard]
          exact q.orthogonal_card_lt H hnd
        have hnz : (q.restrict (q.orthogonal H)).gauss ≠ 0 := by
          rw [q.gauss_orthogonalSplit H hnd] at hq
          exact (mul_ne_zero_iff.mp hq).2
        rw [q.phase_orthogonalSplit H hnd, mul_pow, hphase]
        simpa only [one_mul] using ih _ hlt (q.restrict (q.orthogonal H)) hnz rfl
      · push Not at hani
        obtain ⟨x, hqx, hx⟩ := hani
        let H := AddSubgroup.zmultiples x
        let : Nontrivial H := ⟨⟨⟨x, AddSubgroup.mem_zmultiples x⟩, 0,
          fun h => hx (congrArg Subtype.val h)⟩⟩
        have hH : q.Isotropic H := q.isotropic_zmultiples hqx
        have hlt : Fintype.card (q.orthogonal H ⧸ H.addSubgroupOf (q.orthogonal H)) < n := by
          rw [← hcard]
          exact q.isotropicReduction_card_lt H hH
        have hnz : (q.isotropicReduction H hH).gauss ≠ 0 := by
          rw [q.gauss_isotropicReduction H hH] at hq
          exact (mul_ne_zero_iff.mp hq).2
        rw [q.phase_isotropicReduction H hH]
        exact ih _ hlt (q.isotropicReduction H hH) hnz rfl

end

end OAI.RepresentationTheory.Weil.Local
