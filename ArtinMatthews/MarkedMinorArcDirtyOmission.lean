module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Prime.Defs
public import ArtinMatthews.MarkedMinorArcPrimeProducts
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! Source-ban separation and the actual copied-product omission average in PD04. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem marked_source_ban_product_separation {P D₁ D₂ Z₁ Z₂ : ℕ}
    (hP : 0 < P) (hD₁ : D₁ ∣ P) (hD₂ : D₂ ∣ P)
    (hZ₁ : P.Coprime Z₁) (hZ₂ : P.Coprime Z₂)
    (he : D₁*Z₁ = D₂*Z₂) : D₁ = D₂ ∧ Z₁ = Z₂ := by
  have h12 : D₁ ∣ D₂ := (hZ₂.of_dvd_left hD₁).dvd_of_dvd_mul_right ⟨Z₁,he.symm⟩
  have h21 : D₂ ∣ D₁ := (hZ₁.of_dvd_left hD₂).dvd_of_dvd_mul_right ⟨Z₂,he⟩
  have hd : D₁ = D₂ := Nat.dvd_antisymm h12 h21
  have hpos : 0 < D₁ := Nat.pos_of_dvd_of_pos hD₁ hP
  exact ⟨hd,mul_left_cancel₀ hpos.ne' (by simpa only [hd] using he)⟩

def markedSourceFullProduct {J : Type*} [Fintype J] {M : ℕ}
    (source : J → Fin M → ℕ) : ℕ := ∏ j, ∏ k, source j k

/-- D is the source product after copying all but the one omitted slot in each group. -/
def markedSourceCopiedProduct {J : Type*} [Fintype J] {M : ℕ}
    (source : J → Fin M → ℕ) (choice : J → Fin M) : ℕ :=
  ∏ j, ∏ k ∈ Finset.univ.erase (choice j), source j k

def markedSourceOmittedProduct {J : Type*} [Fintype J] {M : ℕ}
    (source : J → Fin M → ℕ) (choice : J → Fin M) : ℕ := ∏ j, source j (choice j)

theorem markedSourceCopied_mul_omitted {J : Type*} [Fintype J] {M : ℕ}
    (source : J → Fin M → ℕ) (choice : J → Fin M) :
    markedSourceCopiedProduct source choice * markedSourceOmittedProduct source choice =
      markedSourceFullProduct source := by
  rw [markedSourceCopiedProduct,markedSourceOmittedProduct,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact Finset.prod_erase_mul _ _ (Finset.mem_univ (choice j))

theorem markedSourceCopied_dvd_full {J : Type*} [Fintype J] {M : ℕ}
    (source : J → Fin M → ℕ) (choice : J → Fin M) :
    markedSourceCopiedProduct source choice ∣ markedSourceFullProduct source :=
  ⟨markedSourceOmittedProduct source choice,(markedSourceCopied_mul_omitted source choice).symm⟩

theorem markedSourceFull_coprime_of_ban {J : Type*} [Fintype J] {M Z : ℕ}
    (source : J → Fin M → ℕ) (hprime : ∀ j k, (source j k).Prime)
    (hban : ∀ j k, ¬source j k ∣ Z) : (markedSourceFullProduct source).Coprime Z := by
  apply Nat.Coprime.prod_left
  intro j _
  apply Nat.Coprime.prod_left
  intro k _
  exact (hprime j k).coprime_iff_not_dvd.mpr (hban j k)

/-- Full-list distinctness within groups, together with the disjoint prime
bands, makes the literal copied product determine the numeric omission tuple. -/
theorem markedSourceCopiedProduct_injective {J : Type*} [Fintype J] {M : ℕ}
    (P : J → Finset ℕ) (hprime : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (source : J → Fin M → ℕ) (hsource : ∀ j k, source j k ∈ P j)
    (hdist : ∀ j, Function.Injective (source j)) :
    Function.Injective (markedSourceCopiedProduct source) := by
  intro a b hab
  have hp : 0 < markedSourceCopiedProduct source a :=
    Finset.prod_pos (fun j _ => Finset.prod_pos (fun k _ => (hprime j _ (hsource j k)).pos))
  have he : markedSourceOmittedProduct source a = markedSourceOmittedProduct source b := by
    apply mul_left_cancel₀ hp.ne'
    rw [markedSourceCopied_mul_omitted,hab,markedSourceCopied_mul_omitted]
  have hv := marked_disjoint_prime_tuple_eq_of_product_eq P hprime hdis
    (fun j => source j (a j)) (fun j => source j (b j))
    (fun j => hsource j (a j)) (fun j => hsource j (b j)) he
  funext j
  exact hdist j (congrFun hv j)

def markedUniformOmissionWeight {J : Type*} [Fintype J] (M : ℕ) : (J → Fin M) → ℝ :=
  fun _ => ∏ _j : J, 1/(M:ℝ)

theorem markedUniformOmissionWeight_eq {J : Type*} [Fintype J] (M : ℕ) (a : J → Fin M) :
    markedUniformOmissionWeight M a = (M:ℝ)⁻¹^(Fintype.card J) := by
  simp [markedUniformOmissionWeight,one_div]

theorem markedUniformOmissionWeight_total {J : Type*} [Fintype J] [DecidableEq J]
    {M : ℕ} (hM : 0 < M) : (∑ a : J → Fin M, markedUniformOmissionWeight M a) = 1 := by
  simp only [markedUniformOmissionWeight_eq,Finset.sum_const,Finset.card_univ,
    Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]
  rw [← mul_pow,mul_inv_cancel₀ (by exact_mod_cast hM.ne'),one_pow]

/-- The source symmetrization is the uniform product average, so a single
compatible numeric omission tuple has exactly the source factor M^(-K). -/
theorem markedSourceCopiedProduct_fiber_mass {J : Type*} [Fintype J] [DecidableEq J] {M : ℕ}
    (P : J → Finset ℕ) (hprime : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (source : J → Fin M → ℕ) (hsource : ∀ j k, source j k ∈ P j)
    (hdist : ∀ j, Function.Injective (source j)) (a : J → Fin M) :
    (∑ b, if markedSourceCopiedProduct source b = markedSourceCopiedProduct source a then
      markedUniformOmissionWeight M b else 0) = (M:ℝ)⁻¹^(Fintype.card J) := by
  classical
  rw [Fintype.sum_eq_single a]
  · simp only [ite_true,markedUniformOmissionWeight_eq]
  · intro b hba
    have hn : markedSourceCopiedProduct source b ≠ markedSourceCopiedProduct source a :=
      fun he => hba (markedSourceCopiedProduct_injective P hprime hdis source hsource hdist he)
    simp only [hn,ite_false]

end ArtinMatthews
