module

public import ArtinMatthews.MarkedRootProjectiveUniform
public import ArtinMatthews.FixedURootSLOrder
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! Literal squarefree CRT root matrices induce exactly independent uniform
projective kernel lines at the shared primes. -/
namespace ArtinMatthews
open scoped BigOperators LinearAlgebra.Projectivization

instance markedPrimeFactor_prime {S : ℕ} (p : S.primeFactors) : Fact (p : ℕ).Prime :=
  ⟨Nat.prime_of_mem_primeFactors p.2⟩

/-- The actual tuple of residue-field projective lines. -/
abbrev MarkedRootLineTuple (S : ℕ) :=
  ∀ p : S.primeFactors, ℙ (ZMod (p : ℕ)) (Fin 2 → ZMod (p : ℕ))

/-- Exact CRT of the literal squarefree root matrix group. -/
noncomputable def markedSquarefreeRootCRT {S : ℕ} (hS : Squarefree S) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod S) ≃
      (∀ p : S.primeFactors, Matrix.SpecialLinearGroup (Fin 2) (ZMod (p : ℕ))) :=
  (specialLinearRingEquiv (n := Fin 2) (squarefreeZModPrimeEquiv hS)).trans
    (specialLinearPiEquiv (n := Fin 2) (fun p : S.primeFactors => ZMod (p : ℕ)))

/-- The actual first-row kernels of the actual reduced root matrix at each prime. -/
noncomputable def markedRootKernelTuple {S : ℕ} (hS : Squarefree S)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : MarkedRootLineTuple S :=
  fun p => markedMatrixKernelLine ((markedSquarefreeRootCRT hS g) p)

/-- Simultaneous independent finite uniformity, proved by the actual product
SL₂ action. It applies to every complex test of the complete line tuple. -/
theorem marked_finite_product_kernel_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (f : (∀ i, ℙ (F i) (Fin 2 → F i)) → ℂ) :
    (Nat.card (∀ i, Matrix.SpecialLinearGroup (Fin 2) (F i)) : ℂ)⁻¹ *
      (∑ g : ∀ i, Matrix.SpecialLinearGroup (Fin 2) (F i), f (fun i => markedMatrixKernelLine (g i))) =
      (Nat.card (∀ i, ℙ (F i) (Fin 2 → F i)) : ℂ)⁻¹ *
        (∑ ℓ : ∀ i, ℙ (F i) (Fin 2 → F i), f ℓ) := by
  classical
  let G := ∀ i, Matrix.SpecialLinearGroup (Fin 2) (F i)
  let X := ∀ i, ℙ (F i) (Fin 2 → F i)
  let : MulAction G X := inferInstance
  let : MulAction.IsPretransitive G X := {
    exists_smul_eq := fun x y => by
      choose g hg using (fun i => MulAction.exists_smul_eq
        (Matrix.SpecialLinearGroup (Fin 2) (F i)) (x i) (y i))
      exact ⟨g,funext hg⟩ }
  let b : X := fun i => markedVerticalProjectiveLine (F i)
  have hh := marked_finite_pretransitive_average (G := G) b f
  have hinv : (∑ g : G, f (fun i => markedMatrixKernelLine (g i)))=
      ∑ g : G, f (g • b) := by
    have he := Equiv.sum_comp (Equiv.inv G) (fun g : G => f (g • b))
    change (∑ g : G, f (fun i => (g i)⁻¹ • markedVerticalProjectiveLine (F i)))=
      ∑ g : G, f (g • b) at he
    exact he
  rw [hinv]
  simpa only [Fintype.card_eq_nat_card] using hh

/-- Exact source independent-line law for every squarefree root residue.
The redundant NeZero instance follows from squarefreeness and supplies the
finite residue-ring enumeration. No root-counting estimate is an input. -/
theorem marked_squarefree_root_kernel_tuple_average {S : ℕ} [NeZero S]
    (hS : Squarefree S) (f : MarkedRootLineTuple S → ℂ) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℂ)⁻¹ *
      (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S), f (markedRootKernelTuple hS g)) =
      ((∏ p : S.primeFactors, ((p : ℕ)+1) : ℕ) : ℂ)⁻¹ *
        (∑ ℓ : MarkedRootLineTuple S, f ℓ) := by
  classical
  have hsum := Equiv.sum_comp (markedSquarefreeRootCRT hS)
    (fun g => f (fun p => markedMatrixKernelLine (g p)))
  change (∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S), f (markedRootKernelTuple hS g))=
    (∑ g : ∀ p : S.primeFactors, Matrix.SpecialLinearGroup (Fin 2) (ZMod (p : ℕ)),
      f (fun p => markedMatrixKernelLine (g p))) at hsum
  rw [hsum,Nat.card_congr (markedSquarefreeRootCRT hS)]
  have hc : Nat.card (MarkedRootLineTuple S)=∏ p : S.primeFactors, ((p : ℕ)+1) := by
    rw [Nat.card_pi]
    simp only [markedProjectiveLine_card]
  rw [← hc]
  exact marked_finite_product_kernel_average (fun p : S.primeFactors => ZMod (p : ℕ)) f

end ArtinMatthews
