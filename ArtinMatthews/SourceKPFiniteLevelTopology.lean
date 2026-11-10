module

public import ArtinMatthews.SourceKPFiniteLevelDescent
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The finite-level topology is the usual archimedean topology times the
discrete space of finite cosets. Its rational quotient uses the quotient
topology. This does not impose a topology on the finite central cover. -/

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPArchProjective_topology : TopologicalSpace (PGL(2, InfiniteAdeleRing K)) :=
  inferInstanceAs (TopologicalSpace (GL (Fin 2) (InfiniteAdeleRing K) ⧸
    Subgroup.center (GL (Fin 2) (InfiniteAdeleRing K))))

instance sourceKPArchProjective_topologicalGroup : IsTopologicalGroup (PGL(2, InfiniteAdeleRing K)) :=
  inferInstanceAs (IsTopologicalGroup (GL (Fin 2) (InfiniteAdeleRing K) ⧸
    Subgroup.center (GL (Fin 2) (InfiniteAdeleRing K))))

instance sourceKPFiniteLevelFiber_topology : TopologicalSpace (SourceKPFiniteLevelFiber K hζ) := ⊥

instance sourceKPFiniteLevelFiber_discrete : DiscreteTopology (SourceKPFiniteLevelFiber K hζ) := ⟨rfl⟩

theorem sourceKPFiniteLevel_left_continuous (g : SourceKPAdelicProjective K hζ) :
    Continuous (fun x : SourceKPFiniteLevelSpace K hζ => g • x) := by
  change Continuous (fun x : SourceKPFiniteLevelSpace K hζ => (g.1 * x.1, g.2 • x.2))
  exact (continuous_const.mul continuous_fst).prodMk
    ((continuous_of_discreteTopology : Continuous (fun b : SourceKPFiniteLevelFiber K hζ => g.2 • b)).comp
      continuous_snd)

theorem sourceKPFiniteLevel_rational_continuous (γ : PGL(2, K)) :
    Continuous (fun x : SourceKPFiniteLevelSpace K hζ => γ • x) :=
  sourceKPFiniteLevel_left_continuous K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ)

instance sourceKPAutomorphicLevel_topology : TopologicalSpace (SourceKPAutomorphicLevel K hζ) :=
  inferInstanceAs (TopologicalSpace
    (Quotient (MulAction.orbitRel (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ))))

theorem sourceKPFiniteLevelDescend_continuous {V : Type*} [TopologicalSpace V]
    (f : SourceKPAdelicProjective K hζ → V)
    (hf : ∀ g k, f (g * sourceKPFiniteDeepCoverLift K hζ k) = f g)
    (hc : ∀ b : SourceKPFiniteAdeleProjective K hζ,
      Continuous (fun a : PGL(2, InfiniteAdeleRing K) => f (a,b))) :
    Continuous (sourceKPFiniteLevelDescend K hζ f hf) := by
  apply continuous_prod_of_discrete_right.mpr
  intro b
  induction b using Quotient.inductionOn with
  | _ b => exact hc b

theorem sourceKPAutomorphicLevelDescend_continuous {V : Type*} [TopologicalSpace V]
    (f : SourceKPAdelicProjective K hζ → V)
    (hf : ∀ g k, f (g * sourceKPFiniteDeepCoverLift K hζ k) = f g)
    (hr : ∀ γ g, f (sourceKPAdelicProjectiveRationalLift K hζ γ * g) = f g)
    (hc : ∀ b : SourceKPFiniteAdeleProjective K hζ,
      Continuous (fun a : PGL(2, InfiniteAdeleRing K) => f (a,b))) :
    Continuous (sourceKPAutomorphicLevelDescend K hζ f hf hr) :=
  (sourceKPFiniteLevelDescend_continuous K hζ f hf hc).quotient_lift _

end
end ArtinMatthews
