
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Relation.Nullary
open import Relation.Unary hiding (Decidable)
open import Relation.Binary.Core
open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.String
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

module Example where

  data ClassURI : Set where
    OwlThing : ClassURI
    OwlNothing : ClassURI
    AgentURI : ClassURI
    PersonURI : ClassURI 

  data DataPropertyURI : Set where
    OwlTopDataProperty : DataPropertyURI
    OwlBottomDataProperty : DataPropertyURI
    NameURI : DataPropertyURI

  data ObjectPropertyURI : Set where
    OwlTopObjectProperty : ObjectPropertyURI
    OwlBottomObjectProperty : ObjectPropertyURI
    KnowsURI : ObjectPropertyURI

  data DataTypeURI : Set where
    StringURI : DataTypeURI

  data IndividualURI : Set where
    JackURI : IndividualURI
    JillURI : IndividualURI    

  data Literal : Set where
    natLit : ℕ → Literal
    
  data Δᴰ : Set where
    natural : ℕ → Δᴰ
    string : String → Δᴰ

  data Δᴵ : Set where
    C : ClassURI → Δᴵ
    DP : DataPropertyURI → Δᴵ    
    OP : ObjectPropertyURI → Δᴵ
    I : IndividualURI → Δᴵ

  _ᶜ : ClassURI → Pred Δᴵ lzero
  _ᶜ OwlThing x = ⊤
  _ᶜ OwlNothing x = ⊥
  _ᶜ AgentURI (C OwlThing) = ⊥
  _ᶜ AgentURI (C OwlNothing) = ⊤
  _ᶜ AgentURI (C AgentURI) = ⊤
  _ᶜ AgentURI (C PersonURI) = ⊥
  _ᶜ AgentURI (DP x) = ⊥
  _ᶜ AgentURI (OP x) = ⊥
  _ᶜ AgentURI (I x) = ⊥
  _ᶜ PersonURI (C OwlThing) = ⊥
  _ᶜ PersonURI (C OwlNothing) = ⊤
  _ᶜ PersonURI (C AgentURI) = ⊥
  _ᶜ PersonURI (C PersonURI) = ⊤
  _ᶜ PersonURI (DP x) = ⊥
  _ᶜ PersonURI (OP x) = ⊥
  _ᶜ PersonURI (I x) = ⊥
  
  _ᴰᵀ : DataTypeURI → Pred Δᴰ lzero
  _ᴰᵀ StringURI (string x) = ⊤
  _ᴰᵀ StringURI (natural n) = ⊥

  _ᴸᵀ : Literal → Δᴰ
  natLit x ᴸᵀ = natural x

  _ᴰᴾ : DataPropertyURI → Pred (Δᴵ × Δᴰ) lzero
  _ᴰᴾ OwlTopDataProperty y = ⊤
  _ᴰᴾ OwlBottomDataProperty y = ⊥
  _ᴰᴾ NameURI (C x , proj₂) = ⊥
  _ᴰᴾ NameURI (DP OwlTopDataProperty , proj₂) = ⊥ 
  _ᴰᴾ NameURI (DP OwlBottomDataProperty , proj₂) = ⊤
  _ᴰᴾ NameURI (DP NameURI , natural x) = ⊥
  _ᴰᴾ NameURI (DP NameURI , string x) = ⊤
  _ᴰᴾ NameURI (OP x , proj₂) = ⊥
  _ᴰᴾ NameURI (I x , proj₂) = ⊥
  
  _ᴼᴾ : ObjectPropertyURI → Pred (Δᴵ × Δᴵ ) lzero
  _ᴼᴾ OwlTopObjectProperty y = ⊤
  _ᴼᴾ OwlBottomObjectProperty y = ⊥
  _ᴼᴾ KnowsURI (C x , proj₂) = ⊥
  _ᴼᴾ KnowsURI (DP x , proj₂) = ⊥
  _ᴼᴾ KnowsURI (OP x , proj₂) = ⊥
  _ᴼᴾ KnowsURI (I JackURI , C x) = ⊥
  _ᴼᴾ KnowsURI (I JackURI , DP x) = ⊥
  _ᴼᴾ KnowsURI (I JackURI , OP x) = ⊥
  _ᴼᴾ KnowsURI (I JackURI , I JackURI) = ⊤
  _ᴼᴾ KnowsURI (I JackURI , I JillURI) = ⊤
  _ᴼᴾ KnowsURI (I JillURI , C x) = ⊥
  _ᴼᴾ KnowsURI (I JillURI , DP x) = ⊥
  _ᴼᴾ KnowsURI (I JillURI , OP x) = ⊥
  _ᴼᴾ KnowsURI (I JillURI , I JackURI) = ⊤
  _ᴼᴾ KnowsURI (I JillURI , I JillURI) = ⊤

  open import Facet
  _ᶠᴬ : Facet × Literal → Pred Δᴰ lzero
  _ᶠᴬ x y = ⊥
  
  _ᴵ : IndividualURI → Δᴵ
  x ᴵ = I x

  open import OWL
         ClassURI 
         IndividualURI
         DataTypeURI
         DataPropertyURI
         ObjectPropertyURI
         Literal
         Δᴵ
         Δᴰ
         _ᶜ
         _ᴰᵀ
         _ᴸᵀ 
         _ᴵ
         _ᴰᴾ
         _ᴼᴾ
         _ᶠᴬ
         OwlThing
         OwlNothing
         refl
         refl
         OwlTopObjectProperty
         OwlBottomObjectProperty
         refl
         refl
         OwlTopDataProperty
         OwlBottomDataProperty
         refl
         refl
         (λ _ → zero)
         (λ _ → zero)
  
  
