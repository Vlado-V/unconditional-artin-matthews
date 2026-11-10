module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.QuadraticNormAt
public import OAI.RepresentationTheory.Weil.Local.QuadraticNormSubgroup
public import Mathlib.Algebra.QuadraticAlgebra.Basic
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! # Quadratic Norm Units -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticNormUnits.Construction

noncomputable section

/-! Units, conjugation and the norm for the quadratic algebra k[i]. -/

abbrev QuadraticNormAlgebra (k : Type*) [CommRing k] := QuadraticAlgebra k (-1) 0

variable {k : Type*} [Field k]

theorem quadraticAlgebra_norm (z : QuadraticNormAlgebra k) :
    QuadraticAlgebra.norm z = z.re ^ 2 + z.im ^ 2 := by
  simp only [QuadraticAlgebra.norm_def]
  ring

def quadraticNormUnits : (QuadraticNormAlgebra k)ˣ →* kˣ := Units.map QuadraticAlgebra.norm

def quadraticScalarUnits : kˣ →* (QuadraticNormAlgebra k)ˣ :=
  Units.map (algebraMap k (QuadraticNormAlgebra k)).toMonoidHom

def quadraticConjugateUnits : (QuadraticNormAlgebra k)ˣ →* (QuadraticNormAlgebra k)ˣ :=
  Units.map (starRingEnd (QuadraticNormAlgebra k)).toMonoidHom

theorem quadraticNormUnits_scalar (a : kˣ) :
    quadraticNormUnits (quadraticScalarUnits a) = a ^ 2 := by
  apply Units.ext
  change QuadraticAlgebra.norm (algebraMap k (QuadraticNormAlgebra k) a.val) = a.val ^ 2
  exact QuadraticAlgebra.norm_algebraMap a.val

theorem quadraticConjugateUnits_scalar (a : kˣ) :
    quadraticConjugateUnits (quadraticScalarUnits a) = quadraticScalarUnits a := by
  apply Units.ext
  ext <;> simp [quadraticConjugateUnits, quadraticScalarUnits, starRingEnd_apply]

theorem quadraticNormUnits_conjugate (z : (QuadraticNormAlgebra k)ˣ) :
    quadraticNormUnits (quadraticConjugateUnits z) = quadraticNormUnits z := by
  apply Units.ext
  exact QuadraticAlgebra.norm_star z.val

theorem quadraticScalar_norm_eq_mul_conjugate (z : (QuadraticNormAlgebra k)ˣ) :
    quadraticScalarUnits (quadraticNormUnits z) = z * quadraticConjugateUnits z := by
  apply Units.ext
  exact QuadraticAlgebra.algebraMap_norm_eq_mul_star z.val

def quadraticNormOneUnits : QuadraticNormAt.Construction.QuadraticNormOne k →* (QuadraticNormAlgebra k)ˣ where
  toFun p :=
    let z : QuadraticNormAlgebra k := ⟨p.val.1, p.val.2⟩
    have hn : QuadraticAlgebra.norm z = 1 := by rw [quadraticAlgebra_norm]; exact p.property
    have hm : z * star z = 1 := by
      rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, hn, map_one]
    ⟨z, star z, hm, by rw [mul_comm]; exact hm⟩
  map_one' := by apply Units.ext; ext <;> rfl
  map_mul' p q := by
    apply Units.ext
    ext <;> simp [QuadraticNormAt.Construction.QuadraticNormOne.mul_val]
    ring

theorem quadraticNormOneUnits_norm (p : QuadraticNormAt.Construction.QuadraticNormOne k) :
    quadraticNormUnits (quadraticNormOneUnits p) = 1 := by
  apply Units.ext
  change QuadraticAlgebra.norm (⟨p.val.1, p.val.2⟩ : QuadraticNormAlgebra k) = 1
  rw [quadraticAlgebra_norm]
  exact p.property

theorem quadraticNormOneUnits_conjugate (p : QuadraticNormAt.Construction.QuadraticNormOne k) :
    quadraticConjugateUnits (quadraticNormOneUnits p) = (quadraticNormOneUnits p)⁻¹ := by
  apply Units.ext
  rfl

theorem quadraticNormOneUnits_injective : Function.Injective (quadraticNormOneUnits (k := k)) := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : (QuadraticNormAlgebra k)ˣ => z.val.re) hpq
  · exact congrArg (fun z : (QuadraticNormAlgebra k)ˣ => z.val.im) hpq

def quadraticNormOneOfUnit (z : (QuadraticNormAlgebra k)ˣ) (hz : quadraticNormUnits z = 1) :
    QuadraticNormAt.Construction.QuadraticNormOne k := ⟨(z.val.re, z.val.im), by
      change z.val.re ^ 2 + z.val.im ^ 2 = 1
      rw [← quadraticAlgebra_norm]
      exact congrArg Units.val hz⟩

theorem quadraticNormOneUnits_ofUnit (z : (QuadraticNormAlgebra k)ˣ) (hz : quadraticNormUnits z = 1) :
    quadraticNormOneUnits (quadraticNormOneOfUnit z hz) = z := by
  apply Units.ext
  exact QuadraticAlgebra.mk_eta z.val

theorem quadraticNormUnits_range : (quadraticNormUnits (k := k)).range = QuadraticNormSubgroup.Construction.quadraticNormSubgroup k := by
  ext a
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.val.re, z.val.im, (quadraticAlgebra_norm z.val).symm⟩
  · rintro ⟨x, y, hxy⟩
    let z : QuadraticNormAlgebra k := ⟨x, y⟩
    have hn : QuadraticAlgebra.norm z = a.val := (quadraticAlgebra_norm z).trans hxy
    have hu : IsUnit z := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
      (isUnit_iff_ne_zero.mpr (by rw [hn]; exact a.ne_zero))
    refine ⟨hu.unit, ?_⟩
    apply Units.ext
    change QuadraticAlgebra.norm hu.unit.val = a.val
    rw [hu.unit_spec, hn]

end

end OAI.RepresentationTheory.Weil.Local.QuadraticNormUnits.Construction
