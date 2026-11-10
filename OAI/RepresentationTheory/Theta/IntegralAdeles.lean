module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Theta.AdelicSupport
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
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.ProperSpace
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

/-! # Integral Adeles -/

namespace OAI.RepresentationTheory.Theta.IntegralAdeles.PoissonAutomorphyConstruction

noncomputable section

/-! Integral finite adeles as a product of compact local integer rings. -/

open scoped Classical RestrictedProduct
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

def integralProductHomeomorph :
    (∀ v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, v.adicCompletionIntegers ℚ) ≃ₜ AdelicSupport.PoissonAutomorphyConstruction.integralAdele :=
  (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace => v.adicCompletion ℚ)
    (A := fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    (𝓕 := Filter.cofinite)).toHomeomorph.trans
      (Homeomorph.setCongr (by
        rw [RestrictedProduct.range_structureMap]
        rfl))

theorem integralProductHomeomorph_apply
    (x : ∀ v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace, v.adicCompletionIntegers ℚ) (v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    (integralProductHomeomorph x).val v = (x v).val := rfl

instance localIntegerCompact (v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    CompactSpace (v.adicCompletionIntegers ℚ) := by
  let : Algebra ℤ (v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  let : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.symm.compactSpace

instance integralAdeleCompact : CompactSpace AdelicSupport.PoissonAutomorphyConstruction.integralAdele :=
  integralProductHomeomorph.compactSpace

theorem isCompact_integralAdele : IsCompact (AdelicSupport.PoissonAutomorphyConstruction.integralAdele : Set PoissonAutomorphyNormalizationData.AQf) :=
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace AdelicSupport.PoissonAutomorphyConstruction.integralAdele))

theorem localInteger_dense_intCast (v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    DenseRange (fun n : ℤ => (n : v.adicCompletionIntegers ℚ)) := by
  let : Algebra ℤ (v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  let : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let e := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  have h := e.symm.surjective.denseRange.comp PadicInt.denseRange_intCast e.symm.continuous
  simpa only [Function.comp_def, map_intCast] using h

end

end OAI.RepresentationTheory.Theta.IntegralAdeles.PoissonAutomorphyConstruction
