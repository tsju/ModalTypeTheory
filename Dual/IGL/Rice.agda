{-# OPTIONS --without-K #-}

module Dual.IGL.Rice where

open import Data.Nat using (ℕ; suc; zero; _≤_; _<_)
open import Data.Nat.Properties using (<-trans; ≤-refl)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_)
import Data.Product as P
open import Function hiding (_∋_)
open import Dual.IGL

private
  variable
    n : ℕ
    Γ Δ Γ′ Δ′          : Cxt
    A B C              : Type
    M N L M′ N′ L′ M′′ : Δ ︔ Γ ⊢ A

infix 2 _︔_⊢_~_at_
data _︔_⊢_~_at_ (Δ Γ : Cxt) : (M N : Δ ︔ Γ ⊢ A) → ℕ → Set where
  `_ : (x : Γ ∋ A)
       ---------
     → Δ ︔ Γ ⊢ ` x ~ ` x at n

  ƛ_  : Δ ︔ (Γ , A) ⊢ M ~ M′ at n
        ----------------
      → Δ ︔ Γ ⊢ ƛ M ~ ƛ M′ at n

  _·_ : Δ ︔ Γ ⊢ M ~ M′ at n
      → Δ ︔ Γ ⊢ N ~ N′ at n
        ----------
      → Δ ︔ Γ ⊢ (M · N) ~ (M′ · N′) at n

  ⟨⟩    : Δ ︔ Γ ⊢ ⟨⟩ ~ ⟨⟩ at n

  ⟨_,_⟩ : Δ ︔ Γ ⊢ M ~ M′ at n
        → Δ ︔ Γ ⊢ N ~ N′ at n
        → Δ ︔ Γ ⊢ ⟨ M , N ⟩ ~ ⟨ M′ , N′ ⟩ at n

  proj₁_ : Δ ︔ Γ ⊢ M ~ M′ at n
         → Δ ︔ Γ ⊢ proj₁ M ~ proj₁ M′ at n

  proj₂_ : Δ ︔ Γ ⊢ M ~ M′ at n
         → Δ ︔ Γ ⊢ proj₂ M ~ proj₂ M′ at n

  zero : Δ ︔ Γ ⊢ zero ~ zero at n
  
  suc : Δ ︔ Γ ⊢ M ~ M′ at n
      → Δ ︔ Γ ⊢ suc M ~ suc M′ at n

  rec : Δ ︔ Γ ⊢ M ~ M′ at n
      → Δ ︔ Γ , ℕ̇ , _ ⊢ N ~ N′ at n
      → Δ ︔ Γ ⊢ L ~ L′ at n
      → Δ ︔ Γ ⊢ rec M N L ~ rec M′ N′ L′ at n

  mlet_`in_
      : Δ     ︔ Γ ⊢ M ~ M′ at n
      → Δ , A ︔ Γ ⊢ N ~ N′ at n
        ---------
      → Δ ︔ Γ ⊢ mlet M `in N ~ mlet M′ `in N′ at n

  mfix! : (∀ {m} → m < n → Δ ︔  Δ , □ A ⊢ M ~ M′ at m)
        → Δ ︔ Γ ⊢ mfix M ~ mfix M′ at n


~-refl : Δ ︔ Γ ⊢ M ~ M at n
~-refl {M = ` x}          = ` x
~-refl {M = ƛ M}          = ƛ ~-refl
~-refl {M = M · N}        = ~-refl · ~-refl
~-refl {M = ⟨⟩}           = ⟨⟩
~-refl {M = ⟨ M , N ⟩}    = ⟨ ~-refl , ~-refl ⟩
~-refl {M = proj₁ M}      = proj₁ ~-refl
~-refl {M = proj₂ M}      = proj₂ ~-refl
~-refl {M = zero}         = zero
~-refl {M = suc M}        = suc ~-refl
~-refl {M = rec M N L}    = rec ~-refl ~-refl ~-refl
~-refl {M = mlet M `in N} = mlet ~-refl `in ~-refl
~-refl {M = mfix M}       = mfix! λ _ → ~-refl

~-sym : Δ ︔ Γ ⊢ M ~ M′ at n → Δ ︔ Γ ⊢ M′ ~ M at n
~-sym (` x)                = ` x
~-sym (ƛ M~M′)             = ƛ ~-sym M~M′
~-sym (M~M′ · N~N′)        = ~-sym M~M′ · ~-sym N~N′
~-sym ⟨⟩                   = ⟨⟩
~-sym ⟨ M~M′ , N~N′ ⟩      = ⟨ ~-sym M~M′ , ~-sym N~N′ ⟩
~-sym (proj₁ M~M′)         = proj₁ ~-sym M~M′
~-sym (proj₂ M~M′)         = proj₂ ~-sym M~M′
~-sym zero                 = zero
~-sym (suc M)              = suc (~-sym M)
~-sym (rec M N L)          = rec (~-sym M) (~-sym N) (~-sym L)
~-sym (mlet M~M′ `in N~N′) = mlet ~-sym M~M′ `in ~-sym N~N′
~-sym (mfix! f)            = mfix! (λ m<n → ~-sym (f m<n))

~-trans : Δ ︔ Γ ⊢ M ~ M′ at n → Δ ︔ Γ ⊢ M′ ~ M′′ at n → Δ ︔ Γ ⊢ M ~ M′′ at n
~-trans (` x) (` .x) = ` x
~-trans (ƛ M~M′) (ƛ M′~M′′) = ƛ ~-trans M~M′ M′~M′′
~-trans (M~M′ · N~N′) (M′~M′′ · N′~N′′) = ~-trans M~M′ M′~M′′ · ~-trans N~N′ N′~N′′
~-trans ⟨⟩ ⟨⟩ = ⟨⟩
~-trans ⟨ M~M′ , N~N′ ⟩ ⟨ M′~M′′ , N′~N′′ ⟩ = ⟨ ~-trans M~M′ M′~M′′ , ~-trans N~N′ N′~N′′ ⟩
~-trans (proj₁ M~M′) (proj₁ M′~M′′) = proj₁ ~-trans M~M′ M′~M′′
~-trans (proj₂ M~M′) (proj₂ M′~M′′) = proj₂ ~-trans M~M′ M′~M′′
~-trans zero zero = zero
~-trans (suc M~M′) (suc M′~M′′) = suc (~-trans M~M′ M′~M′′)
~-trans (rec L~L′ M~M′ N~N′) (rec L′~L′′ M′~M′′ N′~N′′) = rec (~-trans L~L′ L′~L′′) (~-trans M~M′ M′~M′′) (~-trans N~N′ N′~N′′)
~-trans (mlet M~M′ `in N~N′) (mlet M′~M′′ `in N′~N′′) = mlet ~-trans M~M′ M′~M′′ `in ~-trans N~N′ N′~N′′
~-trans (mfix! f) (mfix! g) = mfix! (λ m<n → ~-trans (f m<n) (g m<n))


~-rename
  : (ρ₁ : Rename Γ Γ′)
  → (ρ₂ : Rename Δ Δ′)
  → Δ  ︔ Γ  ⊢ M ~ M′ at n
  → Δ′ ︔ Γ′ ⊢ rename ρ₁ ρ₂ M ~ rename ρ₁ ρ₂ M′ at n
~-rename ρ₁ ρ₂ (` x)           = ` ρ₁ x
~-rename ρ₁ ρ₂ (ƛ M~M′)        = ƛ ~-rename (ext ρ₁) ρ₂ M~M′
~-rename ρ₁ ρ₂ (M~M′ · N~N′)   = ~-rename ρ₁ ρ₂ M~M′ · ~-rename ρ₁ ρ₂ N~N′
~-rename ρ₁ ρ₂ ⟨⟩              = ⟨⟩
~-rename ρ₁ ρ₂ ⟨ M~M′ , N~N′ ⟩ = ⟨ ~-rename ρ₁ ρ₂ M~M′ , ~-rename ρ₁ ρ₂ N~N′ ⟩
~-rename ρ₁ ρ₂ (proj₁ M~M′)    = proj₁ ~-rename ρ₁ ρ₂ M~M′
~-rename ρ₁ ρ₂ (proj₂ M~M′)    = proj₂ ~-rename ρ₁ ρ₂ M~M′
~-rename ρ₁ ρ₂ zero            = zero
~-rename ρ₁ ρ₂ (suc M)         = suc (~-rename ρ₁ ρ₂ M)
~-rename ρ₁ ρ₂ (rec M N L)     = rec (~-rename ρ₁ ρ₂ M) (~-rename (ext (ext ρ₁)) ρ₂ N) (~-rename ρ₁ ρ₂ L)
~-rename ρ₁ ρ₂ (mlet M~M′ `in N~N′) =
  mlet (~-rename ρ₁ ρ₂ M~M′) `in (~-rename ρ₁ (ext ρ₂) N~N′)
~-rename ρ₁ ρ₂ (mfix! f) = mfix! (λ m<n → ~-rename (ext ρ₂) ρ₂ (f m<n))

~-wk₁
  : Δ ︔ Γ ⊢ M ~ M′ at n
  → Δ ︔ Γ , B ⊢ wk₁ M ~ wk₁ M′ at n
~-wk₁ = ~-rename S_ id

~-exts 
  : {σ σ′ : Subst Δ Γ Γ′}
  → (∀ {A} → (x : Γ ∋ A) → Δ ︔ Γ′ ⊢ σ x ~ σ′ x at n)
  → (∀ {A B} → (x : Γ , B ∋ A) →  Δ ︔ Γ′ , B ⊢ exts σ x ~ exts σ′ x at n)
~-exts σ~σ′ Z     = ` Z
~-exts σ~σ′ (S x) = ~-rename S_ id (σ~σ′ x)

~-⟪⟫
  : {σ σ′ : Subst Δ Γ Γ′}
  → Δ ︔ Γ ⊢ M ~ M′ at n
  → (∀ {A} → (x : Γ ∋ A) → Δ ︔ Γ′ ⊢ σ x ~ σ′ x at n)
  → Δ ︔ Γ′ ⊢ M ⟪ σ ⟫ ~ M′ ⟪ σ′ ⟫ at n
~-⟪⟫ (` x)           σ~σ′ = σ~σ′ x
~-⟪⟫ (ƛ M~M′)        σ~σ′ = ƛ (~-⟪⟫ M~M′ (~-exts σ~σ′))
~-⟪⟫ (M~M′ · N~N′)   σ~σ′ = ~-⟪⟫ M~M′ σ~σ′ · ~-⟪⟫ N~N′ σ~σ′
~-⟪⟫ ⟨⟩              σ~σ′ = ⟨⟩
~-⟪⟫ ⟨ M~M′ , N~N′ ⟩ σ~σ′ = ⟨ ~-⟪⟫ M~M′ σ~σ′ , ~-⟪⟫ N~N′ σ~σ′ ⟩
~-⟪⟫ (proj₁ M~M′)    σ~σ′ = proj₁ ~-⟪⟫ M~M′ σ~σ′
~-⟪⟫ (proj₂ M~M′)    σ~σ′ = proj₂ ~-⟪⟫ M~M′ σ~σ′
~-⟪⟫ zero            σ~σ′ = zero
~-⟪⟫ (suc M)         σ~σ′ = suc (~-⟪⟫ M σ~σ′)
~-⟪⟫ (rec M N L)     σ~σ′ = rec (~-⟪⟫ M σ~σ′) (~-⟪⟫ N (~-exts (~-exts σ~σ′))) (~-⟪⟫ L σ~σ′)
~-⟪⟫ (mlet M~M′ `in N~N′) σ~σ′ =
  mlet ~-⟪⟫ M~M′ σ~σ′ `in ~-⟪⟫ N~N′ (λ x → ~-rename id S_ (σ~σ′ x))
~-⟪⟫ (mfix! f)           σ~σ′ = mfix! f

~-subst-zero
  : Δ ︔ Γ ⊢ N ~ N′ at n
  → (x : Γ , B ∋ A)
  → Δ ︔ Γ ⊢ subst-zero N x ~ subst-zero N′ x at n
~-subst-zero N~N′ Z     = N~N′
~-subst-zero N~N′ (S x) = ` x

~-subst-one-zero
  : Δ ︔ Γ ⊢ M ~ M′ at n
  → Δ ︔ Γ ⊢ N ~ N′ at n
  → (x : Γ , B , C ∋ A)
  → Δ ︔ Γ ⊢ subst-one-zero M N x ~ subst-one-zero M′ N′ x at n
~-subst-one-zero M~M′ N~N′ Z       = N~N′
~-subst-one-zero M~M′ N~N′ (S Z)   = M~M′
~-subst-one-zero M~M′ N~N′ (S S x) = ` x

~-[] : Δ ︔ (Γ , B) ⊢ M ~ M′ at n
     → Δ ︔ Γ       ⊢ N ~ N′ at n
     → Δ ︔ Γ       ⊢ M [ N ] ~ M′ [ N′ ] at n
~-[] M~M′ N~N′ = ~-⟪⟫ M~M′ (~-subst-zero N~N′)

~-[]₂ : Δ ︔ (Γ , B , C) ⊢ L ~ L′ at n
      → Δ ︔ Γ       ⊢ M ~ M′ at n
      → Δ ︔ Γ       ⊢ N ~ N′ at n
      → Δ ︔ Γ       ⊢ L [ M , N ]₂ ~ L′ [ M′ , N′ ]₂ at n
~-[]₂ L~L′ M~M′ N~N′ = ~-⟪⟫ L~L′ (~-subst-one-zero M~M′ N~N′)

~-mexts 
  : {σ σ′ : MSubst Δ Δ′}
  → (∀ {A} → (x : Δ ∋ A) → Δ′ ︔ Δ′ , □ A ⊢ σ x ~ σ′ x at n)
  → (∀ {A B} → (x : Δ , B ∋ A) →  Δ′ , B ︔ Δ′ , B , □ A ⊢ mexts σ x ~ mexts σ′ x at n)
~-mexts σ~σ′ Z     = ` (S Z)
~-mexts σ~σ′ (S x) = ~-rename (ext S_) S_ (σ~σ′ x)

~-m⟪⟫
  : {σ σ′ : MSubst Δ Δ′}
  → Δ ︔ Γ ⊢ M ~ M′ at n
  → (∀ {m} → m < n → ∀ {A} → (x : Δ ∋ A) → Δ′ ︔ Δ′ , □ A ⊢ σ x ~ σ′ x at m)
  → Δ′ ︔ Γ ⊢ M m⟪ σ ⟫ ~ M′ m⟪ σ′ ⟫ at n
~-m⟪⟫ (` x)           σ~σ′ = ` x
~-m⟪⟫ (ƛ M~M′)        σ~σ′ = ƛ ~-m⟪⟫ M~M′ σ~σ′
~-m⟪⟫ (M~M′ · N~N′)   σ~σ′ = ~-m⟪⟫ M~M′ σ~σ′ · ~-m⟪⟫ N~N′ σ~σ′
~-m⟪⟫ ⟨⟩              σ~σ′ = ⟨⟩
~-m⟪⟫ ⟨ M~M′ , N~N′ ⟩ σ~σ′ = ⟨ ~-m⟪⟫ M~M′ σ~σ′ , ~-m⟪⟫ N~N′ σ~σ′ ⟩
~-m⟪⟫ (proj₁ M~M′)    σ~σ′ = proj₁ ~-m⟪⟫ M~M′ σ~σ′
~-m⟪⟫ (proj₂ M~M′)    σ~σ′ = proj₂ ~-m⟪⟫ M~M′ σ~σ′
~-m⟪⟫ zero            σ~σ′ = zero
~-m⟪⟫ (suc M)         σ~σ′ = suc (~-m⟪⟫ M σ~σ′)
~-m⟪⟫ (rec M N L)     σ~σ′ = rec (~-m⟪⟫ M σ~σ′) (~-m⟪⟫ N σ~σ′) (~-m⟪⟫ L σ~σ′)
~-m⟪⟫ (mlet M~M′ `in N~N′) σ~σ′ =
  mlet ~-m⟪⟫ M~M′ σ~σ′ `in ~-m⟪⟫ N~N′ (λ m<n → ~-mexts (σ~σ′ m<n))
~-m⟪⟫ {Δ = Δ} {Δ′ = Δ′} {n = n} {σ = σ} {σ′ = σ′} (mfix! f) σ~σ′ = mfix! λ m<n → ~-⟪⟫ (~-m⟪⟫ (f m<n) λ m′<m x → ~-wk₁ (mσ~mσ′ (<-trans m′<m m<n) x)) (~-exts λ x → mσ~mσ′ m<n x)
  where mσ~mσ′ : (∀ {m} → m < n → ∀ {A} → (x : Δ ∋ A) → Δ′ ︔ Δ′ ⊢  σ x [ mfix σ x ] ~  σ′ x [ mfix σ′ x ] at m) 
        mσ~mσ′ m<n x = ~-[] (σ~σ′ m<n x) (mfix! λ m′<m → σ~σ′ (<-trans m′<m m<n) x)


~-m[]
  : Δ , B ︔ Γ ⊢ M ~ M′ at n
  → (∀ {m} → m < n → Δ ︔ Δ , □ B ⊢ N ~ N′ at m)
  → Δ     ︔ Γ ⊢ M m[ N ] ~ M′ m[ N′ ] at n
~-m[] M~M′ N~N′ = ~-m⟪⟫ M~M′ λ m<n → λ { Z → N~N′ m<n ; (S x) → ` (S x) }

{-
M  --- —→ --- N
|             |
|             |
~             ~
|             |
|             |
M′ --- —→ --- N′
-}

data Leg (n : ℕ) (M′ N : Δ ︔ Γ ⊢ A) : Set where
  leg : ∀ {N′}
    → Δ ︔ Γ ⊢ N ~ N′ at n
    → Δ ︔ Γ ⊢ M′ -→ N′
      --------
    → Leg n M′ N

sim
  : Δ ︔ Γ ⊢ M ~ M′ at n
  → Δ ︔ Γ ⊢ M -→ N
    ---------
  → Leg n M′ N
sim (ƛ M~M′) (ξ-ƛ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (ƛ N~N′) (ξ-ƛ M′-→N′)
sim (M~M′ · M₁~M₁′) (ξ-·₁ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (N~N′ · M₁~M₁′) (ξ-·₁ M′-→N′)
sim (M~M′ · M₁~M₁′) (ξ-·₂ M₁-→N₁) with sim M₁~M₁′ M₁-→N₁
... | leg N₁~N₁′ M₁′-→N₁′ = leg (M~M′ · N₁~N₁′) (ξ-·₂ M₁′-→N₁′)
sim ((mlet M~M′ `in M₁~M₁′) · M₂~M₂′) δ-·-mlet = leg (mlet M~M′ `in M₁~M₁′ · ~-rename id S_ M₂~M₂′) δ-·-mlet
sim ((ƛ M~M′) · M₁~M₁′) β-ƛ· = leg (~-[] M~M′ M₁~M₁′) β-ƛ·
sim (suc M~M′) (ξ-suc M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (suc N~N′) (ξ-suc M′-→N′)
sim (rec M~M′ M₁~M₁′ M₂~M₂′) (ξ-rec₁ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (rec N~N′ M₁~M₁′ M₂~M₂′) (ξ-rec₁ M′-→N′)
sim (rec M~M′ M₁~M₁′ M₂~M₂′) (ξ-rec₂ M₁-→N₁) with sim M₁~M₁′ M₁-→N₁
... | leg N₁~N₁′ M₁′-→N₁′ = leg (rec M~M′ N₁~N₁′ M₂~M₂′) (ξ-rec₂ M₁′-→N₁′)
sim (rec M~M′ M₁~M₁′ M₂~M₂′) (ξ-rec₃ M₂-→N₂) with sim M₂~M₂′ M₂-→N₂
... | leg N₂~N₂′ M₂′-→N₂′ = leg (rec M~M′ M₁~M₁′ N₂~N₂′) (ξ-rec₃ M₂′-→N₂′)
sim (rec M~M′ M₁~M₁′ zero) β-rec-zero = leg M~M′ β-rec-zero
sim (rec M~M′ M₁~M₁′ (suc M₂~M₂′)) β-rec-suc = leg (~-[]₂ M₁~M₁′ M₂~M₂′ (rec M~M′ M₁~M₁′ M₂~M₂′)) β-rec-suc
sim ⟨ M~M′ , M₁~M₁′ ⟩ (ξ-⟨,⟩₁ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (⟨ N~N′ , M₁~M₁′ ⟩) (ξ-⟨,⟩₁ M′-→N′)
sim ⟨ M~M′ , M₁~M₁′ ⟩ (ξ-⟨,⟩₂ M₁-→N₁) with sim M₁~M₁′ M₁-→N₁
... | leg N₁~N₁′ M₁′-→N₁′ = leg (⟨ M~M′ , N₁~N₁′ ⟩) (ξ-⟨,⟩₂ M₁′-→N₁′)
sim (proj₁ M~M′) (ξ-proj₁ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (proj₁ N~N′) (ξ-proj₁ M′-→N′)
sim (proj₁ (mlet M~M′ `in M₁~M₁′)) δ-proj₁-mlet = leg (mlet M~M′ `in (proj₁ M₁~M₁′)) δ-proj₁-mlet
sim (proj₁ ⟨ M~M′ , M₁~M₁′ ⟩) β-⟨,⟩proj₁ = leg M~M′ β-⟨,⟩proj₁
sim (proj₂ M~M′) (ξ-proj₂ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (proj₂ N~N′) (ξ-proj₂ M′-→N′)
sim (proj₂ (mlet M~M′ `in M₁~M₁′)) δ-proj₂-mlet = leg (mlet M~M′ `in (proj₂ M₁~M₁′)) δ-proj₂-mlet
sim (proj₂ ⟨ M~M′ , M₁~M₁′ ⟩) β-⟨,⟩proj₂ = leg M₁~M₁′ β-⟨,⟩proj₂
sim (mlet M~M′ `in M₁~M₁′) (ξ-mlet₁ M-→N) with sim M~M′ M-→N
... | leg N~N′ M′-→N′ = leg (mlet N~N′ `in M₁~M₁′) (ξ-mlet₁ M′-→N′)
sim (mlet M~M′ `in M₁~M₁′) (ξ-mlet₂ M₁-→N₁) with sim M₁~M₁′ M₁-→N₁
... | leg N₁~N₁′ M₁′-→N₁′ = leg (mlet M~M′ `in N₁~N₁′) (ξ-mlet₂ M₁′-→N₁′)
sim (mlet mlet M~M′ `in M₁~M₁′ `in M₂~M₂′) δ-mlet-mlet = leg (mlet M~M′ `in mlet M₁~M₁′ `in ~-rename id (∋-insert-inbetween (∅ , _)) M₂~M₂′) δ-mlet-mlet
sim (mlet (mfix! f) `in M₁~M₁′) β-mfix = leg (~-m[] M₁~M₁′ λ m<n → ~-wk₁ (~-⟪⟫ (f m<n)  (λ { Z → mfix! λ m′<m → f (<-trans m′<m m<n) ; (S x) → ` x }))) β-mfix

data Leg* (n : ℕ) (M′ N : Δ ︔ Γ ⊢ A) : Set where
  leg* : ∀ {N′}
    → Δ ︔ Γ ⊢ N ~ N′ at n
    → Δ ︔ Γ ⊢ M′ -↠ N′
      --------
    → Leg* n M′ N

sim*
  : Δ ︔ Γ ⊢ M ~ M′ at n
  → Δ ︔ Γ ⊢ M -↠ N
    ---------
  → Leg* n M′ N

sim* M~M′ (_ ∎) = leg* M~M′ (_ ∎)
sim* M~M′ (_ -→⟨ M-→M₁ ⟩ M₁-↠N) with sim M~M′ M-→M₁
... | leg M₁~M₁′ M′-→M₁′ with sim* M₁~M₁′ M₁-↠N
... | leg* N~N′ M₁′-→N′ = leg* N~N′ (_ -→⟨ M′-→M₁′ ⟩ M₁′-→N′)

private
  postulate
    confluence 
      : Δ ︔ Γ ⊢ L -↠ M
      → Δ ︔ Γ ⊢ L -↠ M′
      -----------------------------------
      → Σ[ N ∈ Δ ︔ Γ ⊢ A ] ((Δ ︔ Γ ⊢ M -↠ N) × (Δ ︔ Γ ⊢ M′ -↠ N))

rice : {d : ∅ ︔ ∅ ⊢ □ A →̇ ℕ̇}
     → ∅ ︔ ∅ ⊢ (d · (mfix M)) -↠ zero
     → ∅ ︔ ∅ ⊢ (d · (mfix N)) -↠ suc zero
     → ⊥
rice {N = N} dM-↠0 dN-↠1 with sim* (~-refl · (mfix! {n = 0} {M′ = N} (λ ()))) dM-↠0
... | leg* zero dN-↠0 with confluence dN-↠0 dN-↠1
... | _ Data.Product., (_ ∎) Data.Product., (_ -→⟨ ξ-suc () ⟩ _)

-- Logical Relation
infix 2 V[_]∋_~_
infix 2 E[_]∋_~_

mutual
  V[_]∋_~_ : (A : Type) → ∀ {M N} → Value {A = A} M  → Value {A = A} N → Set
  V[ A →̇ B ]∋ ƛ M ~ ƛ N = ∀ {M′ N′} {VM′ : Value M′} {VN′ : Value N′} → V[ A ]∋ VM′ ~ VN′ → E[ B ]∋ M [ M′ ] ~ N [ N′ ]
  V[ □ A ]∋ mfix M ~ mfix N = ⊤
  V[_]∋_~_ ⊤̇ {M = M} {N = N} VM VN = M ≡ N
  V[_]∋_~_ ℕ̇ {M = M} {N = N} VM VN = M ≡ N
  V[_]∋_~_ (A ×̇ B) ⟨ M₁ , M₂ ⟩ ⟨ N₁ , N₂ ⟩ = (E[ A ]∋ M₁ ~ N₁) × (E[ B ]∋ M₂ ~ N₂)

  E[_]∋_~_ : (A : Type) → (M N : ∅ ︔ ∅ ⊢ A) → Set
  E[ A ]∋ M ~ N = ∃[ M′ ] ∃[ N′ ] (∅ ︔ ∅ ⊢ M -↠ M′) × (∅ ︔ ∅ ⊢ N -↠ N′) × Σ[ VM′ ∈  Value M′ ] Σ[ VN′ ∈ Value N′ ] V[ A ]∋ VM′ ~ VN′

  G[_]∋_~_ : (Γ : Cxt) → (σ σ′ : Subst ∅ Γ ∅) → Set
  G[ Γ ]∋ σ ~ σ′ = ∀ {A} (x : Γ ∋ A) → Σ[ Vσx ∈ Value (σ x) ] Σ[ Vσ′x ∈ Value (σ′ x) ] V[ A ]∋ Vσx ~ Vσ′x
  
  Gm[_]∋_~_ : (Δ : Cxt) → (mσ mσ′ : MSubst Δ ∅) → Set
  Gm[ Δ ]∋ σ ~ σ′ = ⊤

E-↠ : E[ A ]∋ M′ ~ N′ → (∅ ︔ ∅ ⊢ M -↠ M′) → (∅ ︔ ∅ ⊢ N -↠ N′) → E[ A ]∋ M ~ N
E-↠ (M′′ P., N′′ P., M′-↠M′′ P., N′-↠N′′ P., VM′′ P., VN′′ P., VM′′~VN′′) M-↠M′ N-↠N′
  = M′′ P., N′′ P., (_ -↠⟨ M-↠M′ ⟩ M′-↠M′′) P., (_ -↠⟨ N-↠N′ ⟩ N′-↠N′′)  P., VM′′ P., VN′′ P., VM′′~VN′′

-- fundamental : (M : Δ ︔ Γ ⊢ A) → ∀ {mσ mσ′ : MSubst Δ ∅} {σ σ′ : Subst ∅ Γ ∅} → G[ Γ ]∋ σ ~ σ′ → E[ A ]∋ M m⟪ mσ ⟫ ⟪ σ ⟫ ~ M m⟪ mσ′ ⟫ ⟪ σ′ ⟫
fundamental : (M : ∅ ︔ ∅ ⊢ A) → E[ A ]∋ M ~ M
fundamental (ƛ M) = ƛ M P., ƛ M P., (ƛ M ∎) P., (ƛ M ∎) P., ƛ M P., ƛ M P., λ V → {! fundamental  !}
fundamental (M · N) with fundamental M | fundamental N
... | ƛ M₁′ P., ƛ M₂′ P., M-↠M₁′ P., M-↠M₂′ P., ƛ VM₁ P., ƛ VM₂ P., VM₁~VM₂  | N₁′ P., N₂′ P., N-↠N₁′ P., N-↠N₂′ P., VN₁ P., VN₂ P., VN₁~VN₂ with VM₁~VM₂ VN₁~VN₂ 
... | MN₁ P., MN₂ P., M[N]₁-↠MN₁ P., M[N]₂-↠MN₂ P., VMN₁ P., VMN₂ P., VMN₁~VMN₂
    = MN₁ P., MN₂ P.,
      (M · N -↠⟨ ·-↠ M-↠M₁′ N-↠N₁′ ⟩ (ƛ M₁′) ·  N₁′ -→⟨ β-ƛ· ⟩ M₁′ [ N₁′ ] -↠⟨ M[N]₁-↠MN₁ ⟩ MN₁ ∎) P.,
      (M · N -↠⟨ ·-↠ M-↠M₂′ N-↠N₂′ ⟩ (ƛ M₂′) ·  N₂′ -→⟨ β-ƛ· ⟩ M₂′ [ N₂′ ] -↠⟨ M[N]₂-↠MN₂ ⟩ MN₂ ∎) P.,
      VMN₁ P., VMN₂ P., VMN₁~VMN₂
fundamental ⟨⟩ = ⟨⟩ P., ⟨⟩ P., (⟨⟩ ∎) P., (⟨⟩ ∎) P., ⟨⟩ P., ⟨⟩ P., refl
fundamental ⟨ M , N ⟩ = ⟨ M , N ⟩ P., ⟨ M , N ⟩ P., (⟨ M , N ⟩ ∎) P., (⟨ M , N ⟩ ∎) P., ⟨ M , N ⟩ P., ⟨ M , N ⟩ P., fundamental M P., fundamental N
fundamental (proj₁ M) with fundamental M
... | ⟨ M₁ , N₁ ⟩ P., ⟨ M₂ , N₂ ⟩ P., M-↠MN₁ P., M-↠MN₂ P., ⟨ .M₁ , .N₁ ⟩ P., ⟨ .M₂ , .N₂ ⟩ P., M₁~M₂ P., N₁~N₂
    = E-↠ M₁~M₂ ((proj₁ M) -↠⟨   proj₁-↠ M-↠MN₁ ⟩ (proj₁ ⟨ M₁ , N₁ ⟩) -→⟨ β-⟨,⟩proj₁ ⟩ (M₁ ∎))
      (((proj₁ M) -↠⟨   proj₁-↠ M-↠MN₂ ⟩ (proj₁ ⟨ M₂ , N₂ ⟩) -→⟨ β-⟨,⟩proj₁ ⟩ (M₂ ∎)))
fundamental (proj₂ M) with fundamental M
... | ⟨ M₁ , N₁ ⟩ P., ⟨ M₂ , N₂ ⟩ P., M-↠M₁ P., M-↠M₂ P., ⟨ .M₁ , .N₁ ⟩ P., ⟨ .M₂ , .N₂ ⟩ P., M₁~M₂ P., N₁~N₂
    = E-↠ N₁~N₂ ((proj₂ M) -↠⟨   proj₂-↠ M-↠M₁ ⟩ (proj₂ ⟨ M₁ , N₁ ⟩) -→⟨ β-⟨,⟩proj₂ ⟩ (N₁ ∎))
      ((proj₂ M) -↠⟨   proj₂-↠ M-↠M₂ ⟩ (proj₂ ⟨ M₂ , N₂ ⟩) -→⟨ β-⟨,⟩proj₂ ⟩ (N₂ ∎))
fundamental zero = zero P., zero P., (zero ∎) P., (zero ∎) P., zero P., zero P., refl
fundamental (suc M) with fundamental M 
... | M₁ P., M₂ P., M-↠M₁ P., M-↠M₂ P., VM₁ P., VM₂ P., refl
    = suc M₁ P., suc M₂ P., suc-↠ M-↠M₁ P., suc-↠ M-↠M₂ P., suc M₁ P., suc M₂ P., refl
fundamental (rec M N L) with fundamental L | fundamental M
... | zero P., .zero P., L-↠zero P., _ P., VL′ P., _ P., refl
    | M₁ P., M₂ P., M-↠M₁ P., M-↠M₂ P., VM₁ P., VM₂ P., VM₁~VM₂ = M₁ P., M₂ P.,
      (rec M N L -↠⟨ rec₃-↠ L-↠zero ⟩ rec M N zero -→⟨ β-rec-zero ⟩ M-↠M₁) P.,
      (rec M N L -↠⟨ rec₃-↠ L-↠zero ⟩ rec M N zero -→⟨ β-rec-zero ⟩ M-↠M₂) P.,
      VM₁ P., VM₂ P., VM₁~VM₂
... | suc L′ P., _ P., L-↠sL′ P., _ P., VsL′ P., _ P., refl | _ = {!   !} P., {!   !}
fundamental (mlet M `in N) = {!   !}
fundamental (mfix M) = mfix M P., mfix M P., (mfix M ∎) P., (mfix M ∎) P., mfix M P., mfix M P., tt

rice₂ : (d : ∅ ︔ ∅ ⊢ □ A →̇ ℕ̇)
     → ∅ ︔ ∅ ⊢ (d · (mfix M)) -↠ zero
     → ∅ ︔ ∅ ⊢ (d · (mfix N)) -↠ suc zero
     → ⊥
rice₂ {A = A} {M = M} {N = N} d dM-↠0 dN-↠1 with fundamental d
... | ƛ d₁ P., ƛ d₂ P., d-↠d₁ P., d-↠d₂ P., ƛ .d₁ P., ƛ .d₂ P., vd₁~vd₂ with vd₁~vd₂ {mfix M} {mfix N} {mfix M} {mfix N} tt
... | n₁ P., n₂ P., -↠n₁ P., -↠n₂ P., vn₁ P., vn₂ P., refl = {!   !}


{-
-- Contextual Equivalence
_∋_~_ : (A : Type) (M N : ∅ ︔ ∅ ⊢ A) → Set
A ∋ M ~ N = ∀ f →  Σ[ k ∈ ℕ ] (∅ ︔ ∅ ⊢ f · M -↠ ℕtoℕ̇ k) × (∅ ︔ ∅ ⊢ f · N -↠ ℕtoℕ̇ k)

go : A ∋ M ~ N at n → A ∋ M ~ N
go M~N f = ∋~-refl f ≤-refl M~N

□∋ : (□ A) ∋ M ~ N at n
□∋ = tt

rice₂ : (d : ∅ ︔ ∅ ⊢ □ A →̇ ℕ̇)
     → ∅ ︔ ∅ ⊢ (d · (mfix M)) -↠ zero
     → ∅ ︔ ∅ ⊢ (d · (mfix N)) -↠ suc zero
     → ⊥
rice₂ {M = M} {N = N} d dM-↠0 dN-↠1 with ∋~-refl {n = 0} d ≤-refl {M₂ = mfix M} {N₂ = mfix N} tt
... | suc k Data.Product., dM-↠k Data.Product., dN-↠k = {!   !} 
... | zero Data.Product., dM-↠k Data.Product., dN-↠k with confluence dN-↠k dN-↠1
... | .zero Data.Product., (.zero ∎) Data.Product., (.(suc zero) -→⟨ ξ-suc () ⟩ _)
  -}  