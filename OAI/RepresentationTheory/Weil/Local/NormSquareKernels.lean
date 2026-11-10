module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.PrincipalSquareClasses
public import OAI.RepresentationTheory.Weil.Local.QuadraticNormAt
public import Mathlib.SetTheory.Cardinal.Finite
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
public import OAI.RepresentationTheory.Weil.Local.SquareIndexTools


set_option backward.privateInPublic true
@[expose] public section

/-! # Norm Square Kernels -/

namespace OAI.RepresentationTheory.Weil.Local.NormSquareKernels.Construction

noncomputable section

/-! Both compact one-dimensional groups have exactly two elements killed by squaring. -/

theorem normUnit_square_kernel_card
    {k : Type*} [NormedField k] [CharZero k] :
    Nat.card (powMonoidHom 2 : PrincipalSquareClasses.Construction.normUnitSubgroup k →* PrincipalSquareClasses.Construction.normUnitSubgroup k).ker = 2 := by
  let ε : PrincipalSquareClasses.Construction.normUnitSubgroup k := ⟨(-1 : kˣ), by change ‖(-1 : k)‖ = 1; simp⟩
  apply SquareIndexTools.Construction.square_kernel_card_two ε
  · intro he
    have hh : (-1 : k) = 1 := congrArg (fun u : PrincipalSquareClasses.Construction.normUnitSubgroup k => u.val.val) he
    norm_num at hh
  · intro x
    constructor
    · intro hx
      have hs : x.val.val ^ 2 = 1 := congrArg (fun u : PrincipalSquareClasses.Construction.normUnitSubgroup k => u.val.val) hx
      rcases sq_eq_one_iff.mp hs with hs | hs
      · left; apply Subtype.ext; exact Units.ext hs
      · right; apply Subtype.ext; exact Units.ext hs
    · rintro (rfl | rfl)
      · exact one_pow 2
      · apply Subtype.ext
        apply Units.ext
        change (-1 : k) ^ 2 = 1
        ring

theorem normOne_square_kernel_card
    {k : Type*} [Field k] [CharZero k] :
    Nat.card (powMonoidHom 2 : QuadraticNormAt.Construction.QuadraticNormOne k →* QuadraticNormAt.Construction.QuadraticNormOne k).ker = 2 := by
  apply SquareIndexTools.Construction.square_kernel_card_two QuadraticNormAt.Construction.QuadraticNormOne.minusOne
  · intro he
    have hh : (-1 : k) = 1 := congrArg (fun p : QuadraticNormAt.Construction.QuadraticNormOne k => p.val.1) he
    norm_num at hh
  · exact QuadraticNormAt.Construction.QuadraticNormOne.sq_eq_one_iff

end

end OAI.RepresentationTheory.Weil.Local.NormSquareKernels.Construction
