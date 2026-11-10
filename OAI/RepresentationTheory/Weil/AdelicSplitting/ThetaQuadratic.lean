module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest
public import OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticGenerators
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterProduct


set_option backward.privateInPublic true
@[expose] public section

/-! # Theta Quadratic -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting

noncomputable section

/-! The prescribed rational quadratic generators preserve the actual
theta sum, by the principal product formula for the supplied character. -/

open scoped Classical _root_.NumberField

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
  (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hu : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ)
  (hp : ∀ q : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) q) = 1)

theorem ThetaQuadratic.Construction.quadratic_localize_rational (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) (q : Fin N → F) (v : ArchimedeanAdeles.Construction.Places F) :
    Local.FunctionsMetaplectic.Construction.quadratic (QuadraticGenerators.Construction.localizeQuadratic F N B v).val (fun i => ArchimedeanAdeles.Construction.rationalScalar F v (q i)) =
      ArchimedeanAdeles.Construction.rationalScalar F v (Local.FunctionsMetaplectic.Construction.quadratic B.val q) := by
  simp only [Local.FunctionsMetaplectic.Construction.quadratic, QuadraticGenerators.Construction.localizeQuadratic, Matrix.map_apply, map_div₀, map_ofNat,
    map_sum, map_mul]

include hc hp in
theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.quadratic_rational_value
    (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalQuadratic F N ψ B a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) (q : Fin N → F) :
    (f.act F N ψ a).value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) =
      f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) := by
  have hv (v : ArchimedeanAdeles.Construction.Places F) :
      (f.act F N ψ a).localValue F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) v =
        Characters.Construction.localAdditiveCharacter F ψ v (ArchimedeanAdeles.Construction.rationalScalar F v (Local.FunctionsMetaplectic.Construction.quadratic B.val q)) *
          f.localValue F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)) v := by
    change (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) N (Characters.Construction.localAdditiveCharacter F ψ v) (a v) (f v)).val
        (fun i => ArchimedeanAdeles.Construction.rationalScalar F v (q i)) = _
    rw [ha.2]
    congr 1
    exact congrArg (Characters.Construction.localAdditiveCharacter F ψ v) (ThetaQuadratic.Construction.quadratic_localize_rational F N B q v)
  have hprod := (CharacterProduct.Construction.localAdditiveCharacter_principal_hasProd F ψ hc hp (Local.FunctionsMetaplectic.Construction.quadratic B.val q)).mul
    (f.localValue_hasProd F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i)))
  simp only [one_mul] at hprod
  have hprod' : HasProd ((f.act F N ψ a).localValue F N
      (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))) (f.value F N (fun i => algebraMap F (ArchimedeanAdeles.Construction.Adeles F) (q i))) := by
    exact hprod.congr_fun hv
  exact ((f.act F N ψ a).localValue_hasProd F N _).unique hprod'

include hc hp in
theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_rational_quadratic
    (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N) (a : Rational.Construction.RestrictedCover F N ψ) (ha : Rational.Construction.IsRationalQuadratic F N ψ B a)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    (f.act F N ψ a).theta F N = f.theta F N := by
  apply tsum_congr
  exact f.quadratic_rational_value F N ψ hc hp B a ha

include hp in
theorem RestrictedTestFamilies.Construction.RestrictedTestFamily.theta_quadratic_family (B : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N)
    (f : RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    (f.act F N ψ (QuadraticGenerators.Construction.rationalQuadraticFamily F N ψ hu hc B)).theta F N = f.theta F N :=
  f.theta_rational_quadratic F N ψ hc hp B _ (QuadraticGenerators.Construction.rationalQuadraticFamily_spec F N ψ hu hc B)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting
