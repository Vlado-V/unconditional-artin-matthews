module

public import ArtinMatthews.MarkedMinorArcRawShiftGeometry
public import ArtinMatthews.MarkedMinorArcRawPrimeBands
public import ArtinMatthews.MarkedMinorArcRawProductMass
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

/-! Exact finite product-variable transport for the actual raw shifted-cell
union, including both endpoint damping factors and the literal tilted mass. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Inclusion of the actual two-cell fiber into the full physical fiber. -/
noncomputable def markedRawShiftFiberInclude {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) (D : ℕ) (root : Z) (shift : ℤ)
    (u : MarkedRawCleanFiber P (markedRawShiftPositionSet hZ r d₀ Y D root shift)) :
    MarkedRawCleanFiber P Z := by
  classical
  exact (⟨u.1.1,(Finset.mem_filter.mp u.1.2).1⟩,u.2)

/-- In the actual shifted-cell union, the determinant divisibility gate is
identically one, by equality of the genuine projective root lines. -/
theorem markedRawShiftFiberInclude_dvd {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) {D : ℕ} (hD : Squarefree D)
    (root : Z) (shift : ℤ)
    (u v : MarkedRawCleanFiber P (markedRawShiftPositionSet hZ r d₀ Y D root shift)) :
    (D : ℤ) ∣ markedMinorIntegerDet u.1.1 v.1.1 := by
  classical
  obtain ⟨_,hu,hul,_⟩ := Finset.mem_filter.mp u.1.2
  obtain ⟨_,hv,hvl,_⟩ := Finset.mem_filter.mp v.1.2
  exact (markedRawPositionLineTuple_eq_iff hD _ _ (hZ _ hu) (hZ _ hv)).mp (hul.symm.trans hvl)

/-- The literal counting conjugate of the actual raw clean matrix, restricted
to the actual two-cell union. -/
noncomputable def markedRawShiftCountingMatrix {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (ν : (j : J) → ↥(P j) → ℝ) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (bg : MarkedRawBackground P pads B)
    (root : Z) (shift : ℤ) : Matrix
      (MarkedRawCleanFiber P (markedRawShiftPositionSet hZ r d₀ Y (markedRawCopiedProduct bg.1) root shift))
      (MarkedRawCleanFiber P (markedRawShiftPositionSet hZ r d₀ Y (markedRawCopiedProduct bg.1) root shift)) ℂ :=
  markedWeightedCountingMatrix (fun u => markedRawLastMass ν u.2)
    ((markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ bg).submatrix
      (markedRawShiftFiberInclude hZ r d₀ Y _ root shift)
      (markedRawShiftFiberInclude hZ r d₀ Y _ root shift))

set_option maxHeartbeats 1000000 in
/-- Exact conjugation by the actual product-variable injection, with all raw
endpoint tests retained. The actual band disjointness discharges the mass
identity; no counting-space norm or distribution assertion is an input. -/
theorem markedRawShiftCountingMatrix_transport_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
      (w : Z → ℤ × ℤ) (q r d₀ Y Q ρ : ℝ) (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
      (bg : MarkedRawBackground (markedRawActualPrimeBand e x) pads B) (root : Z) (shift : ℤ),
      0 < Y → Squarefree (markedRawCopiedProduct bg.1) →
      (d₀ ≤ (markedRawCopiedProduct bg.1 : ℝ) ∧ (markedRawCopiedProduct bg.1 : ℝ) < 2*d₀) →
      markedRawShiftCountingMatrix (markedRawActualPrimeAtom e q x) hZ ψ η r d₀ Y Q ρ χ bg root shift=
        ((d₀/(markedRawCopiedProduct bg.1 : ℝ) : ℝ) : ℂ) •
        markedMinorEndpointMatrix
          ((markedMinorActualMemoryCell e q x ψ η Y Q
            (markedRawCleanShiftCellData hZ r d₀ Y w bg root shift)).submatrix
              markedRawProductMap markedRawProductMap)
          (fun u => markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm
            (bg,markedRawShiftFiberInclude hZ r d₀ Y _ root shift u)))
          (fun u => markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm
            (bg,markedRawShiftFiberInclude hZ r d₀ Y _ root shift u))) := by
  classical
  filter_upwards [markedRawActualLastMass_eq_integerProduct_eventually e hinj] with x hx
  intro pads B Z hZ ψ η w q r d₀ Y Q ρ χ bg root shift hY hD hdyad
  ext u v
  let inc := markedRawShiftFiberInclude (P := markedRawActualPrimeBand e x)
    hZ r d₀ Y (markedRawCopiedProduct bg.1) root shift
  let ep := fun a => markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm (bg,inc a))
  change (Real.sqrt (markedRawLastMass (markedRawActualPrimeAtom e q x) u.2) : ℂ)*
      markedRawCleanKernel hZ ψ η d₀ Y Q ρ χ bg (inc u) (inc v)*
      (Real.sqrt (markedRawLastMass (markedRawActualPrimeAtom e q x) v.2) : ℂ)=
    ((d₀/(markedRawCopiedProduct bg.1 : ℝ) : ℝ) : ℂ)*
      (ep u*((Real.sqrt (markedMinorIntegerProductMass e q x (markedRawLastProduct u.2 : ℤ)) : ℂ)*
        markedMinorActualCleanRawMatrix ψ η (markedRawCopiedProduct bg.1) Y Q
          (markedRawShiftPositionSet hZ r d₀ Y (markedRawCopiedProduct bg.1) root shift)
          (markedRawProductSupport (markedRawActualPrimeBand e x))
          (markedRawProductMap u) (markedRawProductMap v)*
        (Real.sqrt (markedMinorIntegerProductMass e q x (markedRawLastProduct v.2 : ℤ)) : ℂ))*ep v)
  rw [markedRawCleanKernel_factor hZ ψ η d₀ Y Q ρ hY χ bg]
  have hdiv := markedRawShiftFiberInclude_dvd (P := markedRawActualPrimeBand e x) hZ r d₀ Y hD root shift u v
  change (markedRawCopiedProduct bg.1 : ℤ) ∣ markedMinorIntegerDet (inc u).1.1 (inc v).1.1 at hdiv
  rw [ite_eq_left hdyad,ite_eq_left hdiv,hx q u.2,hx q v.2]
  rw [markedMinorActualCleanRawMatrix_apply ψ η _ hY,
    markedMinorActualCleanRawMatrix_apply ψ η _ hY]
  dsimp only [inc,ep,markedRawShiftFiberInclude,markedRawProductMap]
  ring

end ArtinMatthews
