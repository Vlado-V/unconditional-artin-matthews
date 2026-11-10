module

public import ArtinMatthews.SourceKPFiniteOrbit
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

/-! The literal cubic center action on the actual finite-level quotients. -/

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K]

instance sourceKPCubicCenter_topology : TopologicalSpace (rootsOfUnity 3 K) := ⊥

instance sourceKPCubicCenter_discrete : DiscreteTopology (rootsOfUnity 3 K) := ⟨rfl⟩

instance sourceKPCubicCenter_topologicalGroup : IsTopologicalGroup (rootsOfUnity 3 K) :=
  inferInstance

variable [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPCubicCenter_finiteFiberAction :
    MulAction (rootsOfUnity 3 K) (SourceKPFiniteLevelFiber K hζ) :=
  MulAction.compHom _ (sourceKPFiniteAdeleProjectiveCenter K hζ)

instance sourceKPCubicCenter_finiteLevelAction :
    MulAction (rootsOfUnity 3 K) (SourceKPFiniteLevelSpace K hζ) :=
  MulAction.compHom _ (sourceKPAdelicProjectiveCenter K hζ)

theorem sourceKPCubicCenter_finiteLevel_pair (z : rootsOfUnity 3 K)
    (a : PGL(2, InfiniteAdeleRing K)) (b : SourceKPFiniteLevelFiber K hζ) :
    z • (a, b) = (a, z • b) := by
  exact Prod.ext (one_mul a) rfl

theorem sourceKPCubicCenter_finiteLevel_mk (z : rootsOfUnity 3 K)
    (q : SourceKPAdelicProjective K hζ) :
    z • sourceKPFiniteLevelMk K hζ q =
      sourceKPFiniteLevelMk K hζ (sourceKPAdelicProjectiveCenter K hζ z * q) := rfl

theorem sourceKPCubicCenter_deep_commute (z : rootsOfUnity 3 K)
    (k : sourceKPFiniteDeepMatrixGroup K) :
    Commute (sourceKPAdelicProjectiveCenter K hζ z) (sourceKPFiniteDeepCoverLift K hζ k) :=
  sourceKPAdelicProjectiveCenter_commute K hζ z _

instance sourceKPCubicCenter_rationalFiber_comm :
    SMulCommClass (PGL(2, K)) (rootsOfUnity 3 K) (SourceKPFiniteLevelFiber K hζ) where
  smul_comm γ z b := by
    change sourceKPRationalFiniteMap K hζ γ • (sourceKPFiniteAdeleProjectiveCenter K hζ z • b) =
      sourceKPFiniteAdeleProjectiveCenter K hζ z • (sourceKPRationalFiniteMap K hζ γ • b)
    rw [smul_smul, smul_smul, (sourceKPFiniteAdeleProjectiveCenter_commute K hζ z
      (sourceKPRationalFiniteMap K hζ γ)).eq]

instance sourceKPCubicCenter_rationalLevel_comm :
    SMulCommClass (PGL(2, K)) (rootsOfUnity 3 K) (SourceKPFiniteLevelSpace K hζ) where
  smul_comm γ z x := by
    change sourceKPAdelicProjectiveRationalLift K hζ γ • (sourceKPAdelicProjectiveCenter K hζ z • x) =
      sourceKPAdelicProjectiveCenter K hζ z • (sourceKPAdelicProjectiveRationalLift K hζ γ • x)
    rw [smul_smul, smul_smul, (sourceKPAdelicProjectiveCenter_commute K hζ z
      (sourceKPAdelicProjectiveRationalLift K hζ γ)).eq]

instance sourceKPCubicCenter_automorphicAction :
    MulAction (rootsOfUnity 3 K) (SourceKPAutomorphicLevel K hζ) where
  smul z := Quotient.map' (fun x => z • x) (by
    intro x y hxy
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp hxy
    exact MulAction.mem_orbit_iff.mpr
      ⟨γ, (smul_comm γ z y).trans (congrArg (fun x => z • x) hγ)⟩)
  one_smul x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      change Quotient.mk _ ((1 : rootsOfUnity 3 K) • x) = Quotient.mk _ x
      rw [one_smul]
  mul_smul z w x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      change Quotient.mk _ ((z * w) • x) = Quotient.mk _ (z • (w • x))
      rw [mul_smul]

theorem sourceKPCubicCenter_automorphic_mk (z : rootsOfUnity 3 K)
    (q : SourceKPAdelicProjective K hζ) :
    z • sourceKPAutomorphicLevelMk K hζ q =
      sourceKPAutomorphicLevelMk K hζ (sourceKPAdelicProjectiveCenter K hζ z * q) := rfl

instance sourceKPCubicCenter_finiteOrbitAction :
    MulAction (rootsOfUnity 3 K) (SourceKPFiniteOrbit K hζ) where
  smul z := Quotient.map' (fun b => z • b) (by
    intro b c hbc
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp hbc
    exact MulAction.mem_orbit_iff.mpr
      ⟨γ, (smul_comm γ z c).trans (congrArg (fun b => z • b) hγ)⟩)
  one_smul b := by
    induction b using Quotient.inductionOn with
    | _ b =>
      change Quotient.mk _ ((1 : rootsOfUnity 3 K) • b) = Quotient.mk _ b
      rw [one_smul]
  mul_smul z w b := by
    induction b using Quotient.inductionOn with
    | _ b =>
      change Quotient.mk _ ((z * w) • b) = Quotient.mk _ (z • (w • b))
      rw [mul_smul]

theorem sourceKPCubicCenter_finiteOrbit_mk (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) :
    z • sourceKPFiniteOrbitMk K hζ b = sourceKPFiniteOrbitMk K hζ (z • b) := rfl

theorem sourceKPCubicCenter_finiteOrbit_equivariant (z : rootsOfUnity 3 K)
    (x : SourceKPAutomorphicLevel K hζ) :
    sourceKPAutomorphicFiniteOrbit K hζ (z • x) = z • sourceKPAutomorphicFiniteOrbit K hζ x := by
  induction x using Quotient.inductionOn with
  | _ x => rfl

instance sourceKPCubicCenter_finiteFiber_continuousSMul :
    ContinuousSMul (rootsOfUnity 3 K) (SourceKPFiniteLevelFiber K hζ) :=
  ⟨continuous_of_discreteTopology⟩

theorem sourceKPCubicCenter_finiteLevel_continuous (z : rootsOfUnity 3 K) :
    Continuous (fun x : SourceKPFiniteLevelSpace K hζ => z • x) :=
  sourceKPFiniteLevel_left_continuous K hζ (sourceKPAdelicProjectiveCenter K hζ z)

instance sourceKPCubicCenter_finiteLevel_continuousSMul :
    ContinuousSMul (rootsOfUnity 3 K) (SourceKPFiniteLevelSpace K hζ) :=
  ⟨continuous_prod_of_discrete_left.mpr (sourceKPCubicCenter_finiteLevel_continuous K hζ)⟩

theorem sourceKPCubicCenter_automorphic_continuous (z : rootsOfUnity 3 K) :
    Continuous (fun x : SourceKPAutomorphicLevel K hζ => z • x) :=
  (continuous_quot_mk.comp (sourceKPCubicCenter_finiteLevel_continuous K hζ z)).quotient_lift _

instance sourceKPCubicCenter_automorphic_continuousSMul :
    ContinuousSMul (rootsOfUnity 3 K) (SourceKPAutomorphicLevel K hζ) :=
  ⟨continuous_prod_of_discrete_left.mpr (sourceKPCubicCenter_automorphic_continuous K hζ)⟩

instance sourceKPCubicCenter_finiteOrbit_continuousSMul :
    ContinuousSMul (rootsOfUnity 3 K) (SourceKPFiniteOrbit K hζ) :=
  ⟨continuous_of_discreteTopology⟩

def sourceKPCubicCenterFiniteOrbitPerm :
    rootsOfUnity 3 K →* Equiv.Perm (SourceKPFiniteOrbit K hζ) :=
  MulAction.toPermHom _ _

theorem sourceKPCubicCenterFiniteOrbitPerm_apply (z : rootsOfUnity 3 K)
    (o : SourceKPFiniteOrbit K hζ) :
    sourceKPCubicCenterFiniteOrbitPerm K hζ z o = z • o := rfl

end
end ArtinMatthews
