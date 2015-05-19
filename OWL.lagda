\documentclass{article}


%%%%%%%%%%%%%%%%% Preamble %%%%%%%%%%%%%%%%%%%%%%%

%% Fix Margins 
\usepackage[margin=1in]{geometry}

% Fonts
\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{textgreek}
\usepackage{stmaryrd}

%% This handles the translation of unicode to latex:
%\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}

%% Some convenient shorthands
\newcommand{\AD}{\AgdaDatatype}
\newcommand{\AF}{\AgdaFunction}
\newcommand{\AB}{\AgdaBound}
\newcommand{\AIC}{\AgdaInductiveConstructor}
\newcommand{\AM}{\AgdaModule}
\newcommand{\AP}{\AgdaPrimitive}
\newcommand{\AS}{\AgdaString}
% Better use this one!

\usepackage{agda}
%include agda.fmt

\usepackage{bussproofs}

%% Lambda Calculus (should be a .sty at some point) 
\definecolor{typeColour}              {HTML}{0000CD}
\definecolor{judgementColour}         {HTML}{008B00}

\newcommand{\atype}[1]{\textcolor{typeColour}{#1}}

\newcommand{\ofty}[2]{{#1}{:}{#2}}
%\newcommand{\ofty}[2]{{#1}\colon\kern-.15em{#2}}
\newcommand{\bigofty}[2]{{#1} \textcolor{judgementColour}{\;:\;} { \atype{#2} }}
\newcommand{\lam}[3]{\lambda(\ofty{#1}{ \atype{#2} }).{#3}}
\newcommand{\app}[2]{{#1}\circ{#2}}
\newcommand{\bred}{\;\Rightarrow_{\beta}\;}
\newcommand{\subst}[2]{ [{#1} := {#2}] }

\newcommand{\seq}[3]{{#1} \textcolor{judgementColour}{\;\vdash\;} \bigofty{#2}{#3} }

\newcommand{\oseq}[2]{{#1} \textcolor{judgementColour}{\;\vdash\;} {#2}}

\newcommand{\imp}[2]{{#1} \rightarrow {#2}}

\newcommand{\impElim}{$E^{\rightarrow}$}


%% Some characters that are not automatically defined
%% (you figure out by the latex compilation errors you get),
%% and you need to define:
%
%\DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
%\DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
%\DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}
\DeclareUnicodeCharacter{8799}{\ensuremath{\stackrel{?}{=}}}
\DeclareUnicodeCharacter{8759}{\ensuremath{\colon\colon}}
\DeclareUnicodeCharacter{7477}{\ensuremath{^{I}}}
\DeclareUnicodeCharacter{7472}{\ensuremath{^{D}}}
\DeclareUnicodeCharacter{7580}{\ensuremath{^{C}}}
\DeclareUnicodeCharacter{7488}{\ensuremath{^{T}}}
\DeclareUnicodeCharacter{7480}{\ensuremath{^{L}}}
\DeclareUnicodeCharacter{7486}{\ensuremath{^{P}}}
\DeclareUnicodeCharacter{7484}{\ensuremath{^{O}}}
\DeclareUnicodeCharacter{7584}{\ensuremath{^{F}}}
\DeclareUnicodeCharacter{7468}{\ensuremath{^{A}}}
%% Add more as you need them (shouldn’t happen often). 

%% Hyper ref for \url support
\usepackage{hyperref}

%%%%%%%%%%%%%%%%%%% Paper %%%%%%%%%%%%%%%%%%%%%%%%%%


\title{Machine Checkable Formalisation of OWL semantics}
\author{Gavin Mendel-Gleason and Rob Brennan and Kevin Feeney} 

\begin{document}

\maketitle 

%% 1. Who are the intended readers(3-5 names)
%% 2. What did you do?(50 words)
%% 3. Why did you do that?(50 words) - why did it need to be done in the field?
%% 4. What happened when you did it? (50 words)
%% 5. What do the results mean in theory(50 words)
%% 6. What  do the results mean in practice(50 words)
%% 7. (NB most impt q) What is the key benefit for readers?(25 words)
%% 8. What remains unresolved (no word limit)

\begin{abstract} We provide a type theoretic semantics for OWL in
Agda.  This allows us to show that a given model of an OWL description
is sound with respect to the semantics in a machine checkable proof.
A model can be shown to respect the semantics of an OWL description by
constructing a proof term of the appropriate type.  We demonstrate one
simple model and show that it satisfies the associated type.  This
approach can serve as a framework for reasoners to show, by
construction, that the models they produce satisify OWL's semantics.
In the future we hope to provide a practical reasoner for a simple
profile in the OWL semantics.
\end{abstract}

\section{Introduction}

OWL is a language for the specification of ontologies which it
provides with a formal semantics.  OWL is presented in a number of
equivalent syntaxes, which are called {\em descriptions}. 

Generally the meaning of OWL ontologies are explored with a
reasoner\cite{Tai2015Resourceconstrained}.  These will attempt to find
a model for the given {\em description}.  If the model is empty then
the ontology is inconsistent.

We demonstrate how we can realise these models as terms in a Martin
L{\"o}f style type theory (MLTT)\cite{martin1984intuitionistic} such
that the tools for type checking can be leveraged to show the
correctness of reasoners.  Type theories give us a way to cleanly
demonstrate the OWL semantics at the level of types.  For those
comfortable with the account of OWL Full's direct semantics, the
interpretations should look quite familiar, utilising much of the same
notation as the OWL specification.

The approach allows us to mobilise type theory to demonstrate the
correctness results of reasoners. We can also use the formalisation to
prove theories about fragments (for instance decidability results) in
the production of interpretation functions for a model.

We briefly give some basic introduction to techniques for encoding
semantics in type theory, providing examples in Agda.  We then will
outline our encoding of OWL semantics.  We demonstrate an example
theory provided by an OWL description and its associated model.  Using
this model we create the proof obligations from the OWL description
automatically using the function $\AD{|\_|}$.  We then show how the
proof obligations can be filled.  To our knowledge, no formalised
mechanisations of the semantics of OWL 2 of this type exist.

In future work we hope to produce a reasoner which automatically fills
these proof obligations for a specified decidable fragment of OWL and
to supply meaningful constraints on the relationship between the
interpretation functions and the cardinality functions.

\section{Sets in Type Theory}

Martin L{\"o}f style type theories provide a foundational framework
for the exploration of mathematics.  They are however somewhat
different from set theory and so a little bit of {\em boilerplate} is
necessary to conveniently represent objects which are familiar to
those who work with set theory.

One way to represent many of the operations which are present in set
theory is to create a family of {\em unary} predicates over a type.
Agda provides a library which gives us tools to work with this
approach, however we will demonstrate a slightly simpler version to
give an idea of how the approach works.  We will build our example
inside of a record so as to parameterise over a generic {\em small}
set $\AB{A}$.  We then create a function from $\AD{Set}$ to the larger
$\AD{Set₁}$.  This provides us with a family of predicates over the
set A.

\begin{code}

record Sets {A : Set} : Set where

  Pred : Set → Set₁
  Pred A = A → Set

  data ⊤ : Set where
    tt : ⊤
    
  data ⊥ : Set where
  
  infix 3 ¬_
  ¬_ : Set → Set
  ¬ A = A → ⊥ 

\end{code}

This family of unary predicates over $\AB{A}$ will allow us to perform
familiar set-like operations.  We also include two sets, one
representing {\em truth}, $\AD{⊤}$, and which has precisely one
constructor, and another representing {\em falsehood}, $\AD{⊥}$ which
has no constructors at all.  We represent negation constructively as a
map from a type $\AB{A}$ to $\AD{⊥}$.  That is, to prove the negative,
we must supply a function from our logical statement to an unprovable
constant (The type $\AD{⊥}$ has no constructors).  This can only be
done if $\AB{A}$ is inconsistent, and during elimination of $\AB{A}$
we can eliminate all possible cases.  This obviates the need to return
anything, as we never get anything in the first place, which is the
only way we could map to $\AD{⊥}$ as there are no constructors with
which to return a value.

\begin{code}
  
  infix 4 _∈_ _∉_

  _∈_ : A → Pred A → Set
  x ∈ P = P x

  _∉_ : A → Pred A → Set
  x ∉ P = ¬ x ∈ P

\end{code} 

Here we define inclusion as a map, taking an element of type $\AB{A}$
and a predicate from $\AD{Pred}\;\AB{A}$ which merely applies the
predicate to the element.  In this view, various subsets of $\AB{A}$
are formed by producing appropriate predicates.

\begin{code}
  
  _⊆_ : Pred A → Pred A → Set
  P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

  _⇒_ : Pred A → Pred A → Pred A
  P ⇒ Q = λ x → x ∈ P → x ∈ Q
  
\end{code}

We understand $\AB{P}$ to be a subset of \AB{Q} if we are able to
build a map such that if $\AB{P}\;\AB{x}$ holds, then so does
$\AB{Q}\;\AB{x}$.  Similarly we can form a new subset defined by a
predicate which is true precisely when $\AB{P}$ is a subset of
$\AB{Q}$ with the $\AF{\_⇒\_}$ operator.

The other operations of $\AD{∪}$, $\AD{∩}$ etc. are all built
similarly, but we will show a few more examples which are useful for
reading the OWL semantics.

\begin{code}

  ∅ : Pred A 
  ∅ = λ _ → ⊥

  U : Pred A
  U = λ _ → ⊤

  ∁ : Pred A → Pred A
  ∁ P = λ x → x ∉ P

\end{code}

We have the empty set which is modelled as the type of maps to the
uninhabited type $\AD{⊥}$.  Similarly, $\AD{U}$ is modelled as the maps
from $\AB{A}$ to the type of one constructor $\AD{⊤}$.  We form
complement simply by forming a new predicate which holds precisely
when the original predicate does not hold.

In the actual Agda code we utilise Agda's $\AM{Relation.Unary}$
library which allows us to work over sets stratified at different
levels, and so requires the specification of level indicies for
$\AD{Set}$ (see \cite{norell2009dependently}).  These indices will
prove unimportant to us as we are able to stay at level zero, however
they add another parameter to the definition of $\AD{Pred}$, such that
we must now write: $\AD{Pred}\;\AB{A}\;\AB{ℓ}$, for some level index
$\AB{ℓ}$.

\section{OWL Semantics}

\AgdaHide{
\begin{code}
open import Data.Empty
open import Function
open import Data.Unit hiding (setoid ; _≤_ )
open import Data.Product
open import Data.Sum
open import Level
open import Relation.Nullary
open import Relation.Unary hiding (Decidable)
open import Relation.Binary using (Setoid; IsEquivalence) 
open import Relation.Binary.Core hiding (_⇒_)
open import Data.Nat hiding (_⊔_) renaming (suc to nsuc ; zero to nzero)
open import Data.Vec hiding (_∈_)

open import Facet
module Main where

\end{code}
}

The definition of OWL semantics\cite{2012OWL} is given with respect to
a fairly large number of interpretation functions in which the theory
is parametric.  There are, however, a few primitive elements defined,
and a number of laws (for instance the
$\AB{owlTopObjectPropertyLaw}$).

We parameterise this with respect to a given theory using a module.
This module can later be instantiated for some given interpretation
functions and data and object domains as we will demonstrate later. 

\begin{code}

module OWL (ClassURI : Set)
         (IndividualURI : Set)
         (DataTypeURI : Set)
         (DataPropertyURI : Set)
         (ObjectPropertyURI : Set)
         (Literal : Set) -- Constants
         (Δᴵ : Set) -- Object Domain
         (Δᴰ : Set) -- Data Domain
         (_ᶜ : ClassURI → Pred Δᴵ zero) -- Interpretation of classes
         (_ᴰᵀ : DataTypeURI → Pred Δᴰ zero) -- Interpretation of datatypes
         (_ᴸᵀ : Literal → Δᴰ) -- Interpretation of constants
         (_ᴵ : IndividualURI → Δᴵ) -- Interpretation of individuals
         (_ᴰᴾ : DataPropertyURI → Pred (Δᴵ × Δᴰ) zero) -- interpretation of data properties
         (_ᴼᴾ : ObjectPropertyURI → Pred (Δᴵ × Δᴵ ) zero) -- interpretation of object properties
         (_ᶠᴬ : Facet × Literal → Pred Δᴰ zero)
         (owlThing : ClassURI)
         (owlNothing : ClassURI)
         (owlThingLaw : owlThing ᶜ ≡ U)
         (owlNothingLaw : owlNothing ᶜ ≡ ∅)
         (owlTopObjectProperty : ObjectPropertyURI)
         (owlBottomObjectProperty : ObjectPropertyURI)
         (owlTopObjectPropertyLaw : owlTopObjectProperty ᴼᴾ ≡ U)
         (owlBottomObjectPropertyLaw : owlBottomObjectProperty ᴼᴾ ≡ ∅)
         (owlTopDataProperty : DataPropertyURI) 
         (owlBottomDataProperty : DataPropertyURI)
         (owlTopDataPropertyLaw : owlTopDataProperty ᴰᴾ ≡ U)
         (owlBottomDataPropertyLaw : owlBottomDataProperty ᴰᴾ ≡ ∅)
         (♯OP : Pred (Δᴵ × Δᴵ) zero → ℕ) -- cardinality of object properties
         (♯DP : Pred (Δᴵ × Δᴰ) zero → ℕ) -- cardinality of datatype properties
  where

\end{code}

Creating an appropriate datastructure for the syntax of OWL
descriptions in Agda is fairly straightforward and not particularly
enlightening.  We show here only a number of the syntactic elements
which are given by the OWL specification.  Here we have
$\AD{ObjectProperty}$ and $\AD{DataRange}$ specified explicitly as a
datastructure, rather than as a mere parameter to the model.  This is
because these datatypes are composite.

\begin{code}
      
  data ObjectProperty : Set where 
    OP : ObjectPropertyURI → ObjectProperty
    IOP : ObjectPropertyURI → ObjectProperty 

  data DataRange : Set where 
    DataTypeRange : DataTypeURI → DataRange
    DataComplimentOf : DataRange → DataRange
    DataOneOf : ∀ {n} → Vec Literal n → DataRange
    DataTypeRestriction : DataRange → Facet → Literal → DataRange
    
\end{code}

\AgdaHide{

\begin{code}

  data Description : Set where 
    OwlClassURI : ClassURI → Description
    ObjectUnionOf : Description → Description → Description 
    ObjectIntersectionOf : Description → Description → Description 
    ObjectComplementOf : Description → Description
    ObjectOneOf : ∀ {n} → Vec IndividualURI n → Description
    ObjectAllValuesFrom : ObjectProperty → Description → Description
    ObjectSomeValuesFrom : ObjectProperty →  Description → Description 
    ObjectExistsSelf : ObjectProperty → Description
    ObjectHasValue : ObjectProperty → IndividualURI → Description
    ObjectMinCardinality : ℕ → ObjectProperty → Description
    ObjectMaxCardinality : ℕ → ObjectProperty → Description
    ObjectExactCardinality : ℕ → ObjectProperty → Description
    ObjectMinClassCardinality : ℕ → ObjectProperty → Description → Description
    ObjectMaxClassCardinality : ℕ → ObjectProperty → Description → Description
    ObjectExactClassCardinality : ℕ → ObjectProperty → Description → Description
    DataAllValuesFrom : DataPropertyURI → DataRange → Description
    DataSomeValuesFrom : DataPropertyURI → DataRange → Description
    DataHasValue : DataPropertyURI → Literal → Description
    DataMinCardinality : ℕ → DataPropertyURI → Description
    DataMaxCardinality : ℕ → DataPropertyURI → Description
    DataExactCardinality : ℕ → DataPropertyURI → Description
    DataMinRangeCardinality : ℕ → DataPropertyURI → DataRange → Description
    DataMaxRangeCardinality : ℕ → DataPropertyURI → DataRange → Description
    DataExactRangeCardinality : ℕ → DataPropertyURI → DataRange → Description
  
  data ClassAxiom : Set where 
    SubClassOf : Description → Description → ClassAxiom
    EquivalentClasses : Description → Description → ClassAxiom
    DisjointClasses : Description → Description → ClassAxiom
    DisjointUnion : ClassURI → Description → Description → ClassAxiom

  data SubObjectProperty : Set where 
    SubObjectPropertyLift : ObjectProperty → SubObjectProperty
    SubObjectPropertyChain : ObjectProperty → ObjectProperty → SubObjectProperty

  data ObjectPropertyAxiom : Set where 
    SubObjectPropertyOf : SubObjectProperty → ObjectProperty → ObjectPropertyAxiom
    EquivalentObjectProperties : ObjectProperty → ObjectProperty → ObjectPropertyAxiom
    DisjointObjectProperties : ObjectProperty → ObjectProperty → ObjectPropertyAxiom
    InverseObjectProperties : ObjectProperty → ObjectProperty → ObjectPropertyAxiom
    ObjectPropertyDomain : ObjectProperty → Description → ObjectPropertyAxiom 
    ObjectPropertyRange : ObjectProperty → Description → ObjectPropertyAxiom
    FunctionalObjectProperty : ObjectProperty → ObjectPropertyAxiom
    InverseFunctionalObjectProperty : ObjectProperty → ObjectPropertyAxiom
    ReflexiveObjectProperty : ObjectProperty → ObjectPropertyAxiom
    IrreflexiveObjectProperty : ObjectProperty → ObjectPropertyAxiom
    SymetricObjectProperty : ObjectProperty → ObjectPropertyAxiom
    AsymetricObjectProperty : ObjectProperty → ObjectPropertyAxiom
    TransitiveObjectProperty : ObjectProperty → ObjectPropertyAxiom

  data DataPropertyAxiom : Set where 
    SubDataPropertyOf : DataPropertyURI → DataPropertyURI → DataPropertyAxiom
    EquivalentDataProperties : DataPropertyURI → DataPropertyURI → DataPropertyAxiom
    DisjointDataProperties : DataPropertyURI → DataPropertyURI → DataPropertyAxiom
    DataPropertyDomain : DataPropertyURI → Description → DataPropertyAxiom
    DataPropertyRange : DataPropertyURI  → DataRange → DataPropertyAxiom
    FunctionalDataProperty : DataPropertyURI → DataPropertyAxiom
  
  data Fact : Set where 
    SameIndividual : IndividualURI → IndividualURI → Fact
    DifferentIndividuals : IndividualURI → IndividualURI → Fact
    ClassAssertion : ClassURI → IndividualURI → Fact
    ObjectPropertyAssertion : ObjectProperty → IndividualURI → IndividualURI → Fact
    NegativeObjectPropertyAssertion : ObjectProperty → IndividualURI → IndividualURI → Fact
    DataPropertyAssertion : DataPropertyURI → IndividualURI → Literal → Fact
    NegativeDataPropertyAssertion : DataPropertyURI → IndividualURI → Literal → Fact

\end{code}

}


The more interesting part of the code is the translation of rules into
a type which reflects the semantics.  We see below that our various
syntactic descriptions are built up into a $\AD{Rule}$ datatype.
These in turn are collected into a $\AD{Theory}$ which may hold any
finite number of rules.

\begin{code}

  data Rule : Set where 
    FactRule : Fact → Rule
    ClassRule : ClassAxiom → Rule
    ObjectPropertyRule : ObjectPropertyAxiom → Rule
    DataProperytRule : DataPropertyAxiom → Rule
  
  Theory : ℕ → Set
  Theory n = Vec Rule n
  
\end{code}

To translate our theory into its appropriate type we need a few
interpretation functions which translate the various syntactic
categories into types.

First we define the meaning of a $\AF{domain}$ and a $\AF{range}$.  To
do this, we use Agda's $\AD{Σ}$ which is essentially an existential
type.  This type is inhabited by a pair composed of a witness, and
then a proof that the witness has some property.  In the example of
$\AF{domain}$ below, we see that we produce a predicate, taking an
argument of type $(\AB{A}\;\AD{×}\;\AB{B})$ (the type of cartesian
pairs, which in this case is used to model properties), we then
produce a $\AD{Σ}$ type which can be inhabited by a pair of an element
of $\AB{B}$ and a proof that the property $p$ holds over
$(\AB{x}\;\AIC{,}\;\AB{y})$.  It is worth noting that we do not
concern ourselves with partial predicates - there must be an element
of the range for an element to be considered part of the domain, and
vice-versa.

\begin{code}

  domain : ∀ {A B : Set} → Pred (A × B) zero  → Pred A zero 
  domain {A} {B} p = λ x → Σ[ y ∈ B ] (x , y) ∈ p

  range : ∀ {A B : Set} → Pred (A × B) zero  → Pred B zero 
  range {A} {B} p = λ y → Σ[ x ∈ A ] (x , y) ∈ p

\end{code}

The interpretation of $\AD{DataRange}$ produces a predicate over the
data domain type $\AB{Δᴰ}$.  For $\AIC{DataTypeRange}$, we obtain our
interpretation from the data type interpretation function which is a
parameter to the model.  For $\AIC{DataComplementOf}$, we merely form
the complement of the predicate.  The $\AIC{DataOneOf}$ constructor is
slightly more involved.  Here we produce a new predicate as a fold
over a vector of enumerated data types.  The fold is a finite union
which produces a proof obligation to show that an element which
satisfies the predicate must be $\AD{\_≡\_}$ to the literal for some
literal $\AB{c}$.

\begin{code}

  ∣_∣dr : DataRange → Pred Δᴰ zero
  ∣ DataTypeRange t ∣dr = t ᴰᵀ
  ∣ DataComplimentOf r ∣dr = ∁ ∣ r ∣dr 
  ∣ DataOneOf v ∣dr = foldr (λ _ → Pred Δᴰ zero) (λ c p → (λ x → x ≡ c ᴸᵀ) ∪ p) ∅ v 
  ∣ DataTypeRestriction r x x₁ ∣dr = ∣ r ∣dr ∩ (x , x₁) ᶠᴬ
  
\end{code}

The translation of $\AD{ObjectProperty}$ and $\AD{SubObjectProperty}$
is particularly straightforward.  In the case of SubObjectProperty we
use the function $\AF{\_⇒\_}$ which is essentially just a synonym for
subset but which produces a predicate over the type
$(\AB{Δᴵ}\;\AD{×}\;\AB{Δᴵ})$ rather than a $\AD{Set}$.

\begin{code}

  ∣_∣op : ObjectProperty → Pred (Δᴵ × Δᴵ) zero
  ∣_∣op (OP x) = x ᴼᴾ 
  ∣_∣op (IOP x) = ∁ (x ᴼᴾ)

  ∣_∣sop : SubObjectProperty → Pred (Δᴵ × Δᴵ) zero
  ∣_∣sop (SubObjectPropertyLift p) = ∣ p ∣op 
  ∣_∣sop (SubObjectPropertyChain p q) = ∣ p ∣op ⇒ ∣ q ∣op

\end{code}

We then come to the interpretation of classes.  We omit the
cardinality constraints for reasons of space.  Again the structure
follows very closely from the interpretations given in the
specification.  Perhaps of note is $\AIC{ObjectAllValuesFrom}$ which
produces a proof obligation that a function is produced which has the
entire domain of individuals as its argument, and
$\AIC{ObjectSomeValuesFrom}$ which produces a $\AD{Σ}$ type requiring
that inhabitants provide the witnessing element from the domain of
individuals.

\begin{code}

  ∣_∣c : Description → Pred Δᴵ zero
  ∣ OwlClassURI x ∣c = x ᶜ
  ∣ ObjectUnionOf xc xc₁ ∣c = ∣ xc ∣c ∪ ∣ xc₁ ∣c 
  ∣ ObjectIntersectionOf x x₁ ∣c = ∣ x ∣c ∩ ∣ x₁ ∣c
  ∣ ObjectComplementOf x ∣c = ∁ (∣ x ∣c)
  ∣ ObjectOneOf v ∣c = foldr (λ _ → Pred Δᴵ zero) (λ y p → (λ x → x ≡ y ᴵ) ∪ p) ∅ v
  ∣ ObjectAllValuesFrom p c ∣c = λ x → ∀ (y : Δᴵ) → (x , y) ∈ ∣ p ∣op → y ∈ ∣ c ∣c
  ∣ ObjectSomeValuesFrom p c ∣c = λ x → Σ[ y ∈ Δᴵ ] (x , y) ∈ ∣ p ∣op × y ∈ ∣ c ∣c
  ∣ ObjectExistsSelf p ∣c = λ x → (x , x) ∈ ∣ p ∣op 
  ∣ ObjectHasValue (OP p) v ∣c = λ x → (x , v ᴵ) ∈ p ᴼᴾ
  ∣ ObjectHasValue (IOP p) v ∣c = ∁ (λ x → (x , v ᴵ) ∈ p ᴼᴾ)
\end{code}
\AgdaHide{
  \begin{code}
  ∣ ObjectMinCardinality n p ∣c = λ x → ♯OP( λ prop → prop ∈ ∣ p ∣op × x ∈ domain ∣ p ∣op ) ≥ n
  ∣ ObjectMaxCardinality n p ∣c = λ x → ♯OP (λ prop → prop ∈ ∣ p ∣op × x ∈ domain ∣ p ∣op) ≤ n
  ∣ ObjectExactCardinality n p ∣c = λ x → ♯OP (λ prop → prop ∈ ∣ p ∣op × x ∈ domain ∣ p ∣op) ≡ n
  ∣ ObjectMinClassCardinality n p c ∣c = λ x → ♯OP( λ prop → (prop ∈ ∣ p ∣op) × x ∈ domain ∣ p ∣op × proj₂ prop ∈ ∣ c ∣c ) ≥ n
  ∣ ObjectMaxClassCardinality n p c ∣c = λ x → ♯OP (λ prop → prop ∈ ∣ p ∣op × x ∈ domain ∣ p ∣op  × proj₂ prop ∈ ∣ c ∣c ) ≤ n
  ∣ ObjectExactClassCardinality n p c ∣c = λ x → ♯OP (λ prop → prop ∈ ∣ p ∣op × x ∈ domain ∣ p ∣op × proj₂ prop ∈ ∣ c ∣c ) ≡ n
  \end{code}
}
\begin{code}
  ∣ DataAllValuesFrom p x₁ ∣c = λ x → ∀ y → y ∈ p ᴰᴾ → proj₂ y ∈ ∣ x₁ ∣dr
  ∣ DataSomeValuesFrom p x₁ ∣c = λ x → Σ[ y ∈ (Δᴵ × Δᴰ) ] (y ∈ p ᴰᴾ → proj₂ y ∈ ∣ x₁ ∣dr)
  ∣ DataHasValue p c ∣c = λ x → Σ[ y ∈ Δᴰ ] (y ≡ c ᴸᵀ × (x , y) ∈ p ᴰᴾ)

\end{code}
\AgdaHide{
  \begin{code}
  ∣ DataMinCardinality n p ∣c  = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ)) ≥ n
  ∣ DataMaxCardinality n p ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ)) ≤ n
  ∣ DataExactCardinality n p ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ)) ≡ n
  ∣ DataMinRangeCardinality n p r ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ) × proj₂ prop ∈ ∣ r ∣dr) ≥ n
  ∣ DataMaxRangeCardinality n p r ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ) × proj₂ prop ∈ ∣ r ∣dr) ≤ n
  ∣ DataExactRangeCardinality n p r ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ) × proj₂ prop ∈ ∣ r ∣dr) ≡ n
  \end{code}
}

The function $\AF{∣\_∣r}$ is responsible for the interpretation of
rules, which is a map from the $\AD{Rule}$ to $\AD{Set}$ and gives us
the proof obligations required for a single rule.

\begin{code}

  ∣_∣r : Rule → Set
  ∣ FactRule (SameIndividual x x₁) ∣r = x ᴵ ≡ x₁ ᴵ 
  ∣ FactRule (DifferentIndividuals x x₁) ∣r = x ᴵ ≡ x₁ ᴵ → ⊥
  ∣ FactRule (ClassAssertion C x) ∣r =  x ᴵ ∈ C ᶜ
  ∣ FactRule (ObjectPropertyAssertion (OP x) x₁ x₂) ∣r = (x₁ ᴵ , x₂ ᴵ) ∈ x ᴼᴾ
  ∣ FactRule (ObjectPropertyAssertion (IOP x) x₁ x₂) ∣r = (x₂ ᴵ , x₁ ᴵ) ∈ x ᴼᴾ
  ∣ FactRule (NegativeObjectPropertyAssertion (OP x) x₁ x₂) ∣r = (x₁ ᴵ , x₂ ᴵ) ∉ x ᴼᴾ
  ∣ FactRule (NegativeObjectPropertyAssertion (IOP x) x₁ x₂) ∣r = (x₂ ᴵ , x₁ ᴵ) ∉ x ᴼᴾ
  ∣ FactRule (DataPropertyAssertion p x l) ∣r = (x ᴵ , l ᴸᵀ) ∈ p ᴰᴾ
  ∣ FactRule (NegativeDataPropertyAssertion p x l) ∣r = (x ᴵ , l ᴸᵀ) ∉ p ᴰᴾ
  ∣ ClassRule (SubClassOf sub super) ∣r = ∣ sub ∣c ⊆ ∣ super ∣c
  ∣ ClassRule (EquivalentClasses a b) ∣r = ∣ a ∣c ⊆ ∣ b ∣c × ∣ b ∣c ⊆ ∣ a ∣c
  ∣ ClassRule (DisjointClasses a b) ∣r = ∣ a ∣c ∩ ∣ b ∣c ⊆ ∅
  ∣ ClassRule (DisjointUnion c a b) ∣r = c ᶜ ⊆ ∣ a ∣c ∪ ∣ b ∣c × ∣ a ∣c ∩ ∣ b ∣c ⊆ ∅
  ∣ ObjectPropertyRule (SubObjectPropertyOf sub super) ∣r = ∣ sub ∣sop ⊆ ∣ super ∣op
  ∣ ObjectPropertyRule (EquivalentObjectProperties a b) ∣r = ∣ a ∣op ⊆ ∣ b ∣op × ∣ b ∣op ⊆ ∣ a ∣op
  ∣ ObjectPropertyRule (DisjointObjectProperties a b) ∣r = ∣ a ∣op ∩ ∣ b ∣op ⊆ ∅
  ∣ ObjectPropertyRule (InverseObjectProperties a b) ∣r =
    ∀ x y → (x , y) ∈ ∣ a ∣op × (y , x) ∈ ∣ b ∣op
  ∣ ObjectPropertyRule (ObjectPropertyDomain p c) ∣r = ∀ x y → (x , y) ∈ ∣ p ∣op → x ∈ ∣ c ∣c
  ∣ ObjectPropertyRule (ObjectPropertyRange p c) ∣r = ∀ x y → (x , y) ∈ ∣ p ∣op → y ∈ ∣ c ∣c
  ∣ ObjectPropertyRule (FunctionalObjectProperty p) ∣r =
    ∀ x y y' → (x , y) ∈ ∣ p ∣op × (x , y') ∈ ∣ p ∣op → y ≡ y'
  ∣ ObjectPropertyRule (InverseFunctionalObjectProperty p) ∣r =
    ∀ x x' y → (x , y) ∈ ∣ p ∣op × (x' , y) ∈ ∣ p ∣op → x ≡ x'
  ∣ ObjectPropertyRule (ReflexiveObjectProperty p) ∣r = ∀ x → (x , x) ∈ ∣ p ∣op
  ∣ ObjectPropertyRule (IrreflexiveObjectProperty p) ∣r = ∀ x → (x , x) ∉ ∣ p ∣op
  ∣ ObjectPropertyRule (SymetricObjectProperty p) ∣r = ∀ x y → (x , y) ∈ ∣ p ∣op × (y , x) ∈ ∣ p ∣op
  ∣ ObjectPropertyRule (AsymetricObjectProperty p) ∣r = ∀ x y → (x , y) ∈ ∣ p ∣op → (y , x) ∉ ∣ p ∣op
  ∣ ObjectPropertyRule (TransitiveObjectProperty p) ∣r =
    ∀ x y z → (x , y) ∈ ∣ p ∣op × (y , z) ∈ ∣ p ∣op → (x , z) ∈ ∣ p ∣op
  ∣ DataProperytRule (SubDataPropertyOf a b) ∣r = a ᴰᴾ ⊆ b ᴰᴾ
  ∣ DataProperytRule (EquivalentDataProperties a b) ∣r = a ᴰᴾ ⊆ b ᴰᴾ × b ᴰᴾ ⊆ a ᴰᴾ
  ∣ DataProperytRule (DisjointDataProperties a b) ∣r = a ᴰᴾ ∩ b ᴰᴾ ⊆ ∅
  ∣ DataProperytRule (DataPropertyDomain p c) ∣r = ∀ x y → (x , y) ∈ p ᴰᴾ → x ∈ ∣ c ∣c
  ∣ DataProperytRule (DataPropertyRange p dr) ∣r = ∀ x y → (x , y) ∈ p ᴰᴾ → y ∈ ∣ dr ∣dr
  ∣ DataProperytRule (FunctionalDataProperty p) ∣r =
    ∀ x y y' → (x , y) ∈ p ᴰᴾ × (x , y') ∈ p ᴰᴾ → y ≡ y'
  
\end{code}

Lastly $\AF{∣\_∣}$ is the very simple function which takes us from a
vector of rules to the cartesian product of the types associated with
each of these rules, essentially translating the vector rules into a chain of
proof obligations.

\begin{code}

  ∣_∣ : ∀ {n} → Theory n → Set
  ∣ [] ∣ = ⊤
  ∣ x ∷ t ∣ = ∣ x ∣r × ∣ t ∣

\end{code}

\section{Example}

\AgdaHide{
  \begin{code}
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Vec hiding (_∈_)
open import Relation.Nullary
open import Relation.Unary hiding (Decidable)
open import Relation.Binary.Core
open import Level renaming (zero to lzero ; suc to lsuc)
open import Data.String renaming (_≟_ to _≟s_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.TrustMe
  \end{code}
}

So how does this work in practice?  We produce a very simple theory in
order to look at the structure of the proof obligations produced.
First, we need to have concrete representatives of all of our
individuals, including classes, data properties, data types etc.  The
representation is quite open to us as we must also supply the
interpretation functions and the data and individual domains.  For
simplicity we have represented everything as inductive types.  Our
data domain ($\AD{Δᴰ}$) is composed only of strings and natural
numbers, whereas our invidual domain ($\AD{Iᴰ}$) is composed of
classes, object properties, data properties, and individuals.

\begin{code}

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

\end{code}

From this point we can begin representing our interpretation
functions.  These interpretation functions take us from a given URI to
a predicate over the appropriate domain.  Here we see that the class
interpretation function takes an $\AIC{OwlThing}$, $\AIC{OwlNothing}$,
$\AIC{AgentURI}$, $\AIC{PersonURI}$ and produces either $\AD{⊤}$ or
$\AD{⊥}$.  That $\AIC{OwlThing}$, $\AIC{OwlNothing}$ be in the domain
is a requirement in order to satisfy the laws necessary to open the
$\AM{OWL}$ module.

\begin{code}

  _ᶜ : ClassURI → Pred Δᴵ lzero
  _ᶜ OwlThing x = ⊤
  _ᶜ OwlNothing x = ⊥
  _ᶜ AgentURI (C x) = ⊥
  _ᶜ AgentURI (DP x) = ⊥
  _ᶜ AgentURI (OP x) = ⊥
  _ᶜ AgentURI (I JackURI) = ⊤
  _ᶜ AgentURI (I JillURI) = ⊤
  _ᶜ PersonURI (C x) = ⊥
  _ᶜ PersonURI (DP x) = ⊥
  _ᶜ PersonURI (OP x) = ⊥
  _ᶜ PersonURI (I JackURI) = ⊤
  _ᶜ PersonURI (I JillURI) = ⊤

\end{code}

Here we have the interetations of datatypes and the function which
maps from literals into the data domain. 

\begin{code}

  _ᴰᵀ : DataTypeURI → Pred Δᴰ lzero
  _ᴰᵀ StringURI (string x) = ⊤
  _ᴰᵀ StringURI (natural n) = ⊥

  _ᴸᵀ : Literal → Δᴰ
  natLit x ᴸᵀ = natural x
  
\end{code}

The interprentation function for data and object properties encodes
the triples of our graph.  Each triple ending at $\AD{⊥}$ is known not
to exist. Each ending at $\AD{⊤}$ is considered to be present.  One
can see immediately that the $\AIC{OwlTopDataProperty}$ exists for
everything in the domain and range as the argument $\AB{y}$ is
uninspected.

Our literals $\AS{"Jack"}$ and $\AS{"Jill"}$ are encoded by checking
that the strings are equal to a given string, and producing the proof
of equivalence.

\begin{code}

  _ᴰᴾ : DataPropertyURI → Pred (Δᴵ × Δᴰ) lzero
  _ᴰᴾ OwlTopDataProperty y = ⊤
  _ᴰᴾ OwlBottomDataProperty y = ⊥
  _ᴰᴾ NameURI (C x , proj₂) = ⊥
  _ᴰᴾ NameURI (DP x , proj₂) = ⊥
  _ᴰᴾ NameURI (OP x , proj₂) = ⊥
  _ᴰᴾ NameURI (I JackURI , natural x) = ⊥
  _ᴰᴾ NameURI (I JackURI , string x) with x ≟s "Jack"
  _ᴰᴾ NameURI (I JackURI , string x) | yes p = ⊤
  _ᴰᴾ NameURI (I JackURI , string x) | no ¬p = ⊥
  _ᴰᴾ NameURI (I JillURI , natural x) = ⊥
  _ᴰᴾ NameURI (I JillURI , string x) with x ≟s "Jill"
  _ᴰᴾ NameURI (I JillURI , string x) | yes p = ⊤
  _ᴰᴾ NameURI (I JillURI , string x) | no p = ⊥
  
  _ᴼᴾ : ObjectPropertyURI → Pred (Δᴵ × Δᴵ ) lzero
  _ᴼᴾ OwlTopObjectProperty y = ⊤
  _ᴼᴾ OwlBottomObjectProperty y = ⊥
  _ᴼᴾ KnowsURI (C x , proj₂) = ⊥
  _ᴼᴾ KnowsURI (DP x , proj₂) = ⊥
  _ᴼᴾ KnowsURI (OP x , proj₂) = ⊥
  _ᴼᴾ KnowsURI (I x , C y) = ⊥
  _ᴼᴾ KnowsURI (I x , DP y) = ⊥
  _ᴼᴾ KnowsURI (I x , OP y) = ⊥
  _ᴼᴾ KnowsURI (I x , I y) with x | y
  _ᴼᴾ KnowsURI (I x , I y) | JackURI | JackURI = ⊤
  _ᴼᴾ KnowsURI (I x , I y) | JackURI | JillURI = ⊤
  _ᴼᴾ KnowsURI (I x , I y) | JillURI | JackURI = ⊤
  _ᴼᴾ KnowsURI (I x , I y) | JillURI | JillURI = ⊤

\end{code}

We supply a completely empty facet interpretation function as we don't
make use of facets in this particular theory.  Our invidiual URI
embedding is straightforward in that it just uses the $\AIC{I}$
constructor to embed in the $\AD{Δᴵ}$ individual domain.

\begin{code} 

  _ᶠᴬ : Facet × Literal → Pred Δᴰ lzero
  _ᶠᴬ x y = ⊥
  
  _ᴵ : IndividualURI → Δᴵ
  x ᴵ = I x

\end{code}

With the various interpretation functions, domains and resources
established, we can proceed to open the OWL module which provides us
with the semantic interpertation.  Note here the use of $\AIC{refl}$
which is the proof of correctness of the various laws which OWL must
have satisfied with respect to the top and bottom properties.  

\begin{code}

  open OWL ClassURI IndividualURI DataTypeURI DataPropertyURI ObjectPropertyURI Literal
         Δᴵ Δᴰ _ᶜ _ᴰᵀ _ᴸᵀ _ᴵ _ᴰᴾ _ᴼᴾ _ᶠᴬ
         OwlThing OwlNothing refl refl
         OwlTopObjectProperty OwlBottomObjectProperty refl refl
         OwlTopDataProperty OwlBottomDataProperty refl refl (λ _ → nzero) (λ _ → nzero)

\end{code}

Finally we are able to see the semantics in action.  We first write
down the rules we would like to be true of our model in
$\AF{myTheory}$.  We do leave an $\AB{\_}$ so that Agda fills in the
appropriate natural number which counts the number of rules we have
provided.  In this case we ask that the following constraints be
fulfilled: $\AIC{AgentURI} ⊆ \AIC{OwlThing}$ $\AIC{PersonURI} ⊆ \AIC{AgentURI}$ 
and that the property $\AIC{KnowsURI}$ has a range and domain of $\AIC{AgentURI}$.

\begin{code}

  myTheory : Theory _
  myTheory = ClassRule (SubClassOf (OwlClassURI AgentURI)
                                   (OwlClassURI OwlThing)) ∷
             ClassRule (SubClassOf (OwlClassURI PersonURI)
                                   (OwlClassURI AgentURI)) ∷
             ObjectPropertyRule (ObjectPropertyRange (OP KnowsURI)
                                                     (OwlClassURI AgentURI)) ∷
             ObjectPropertyRule (ObjectPropertyDomain (OP KnowsURI)
                                                      (OwlClassURI AgentURI)) ∷ []

\end{code} 

We can then apply the $\AF{∣\_∣}$ to $\AF{myTheory}$.  To see what the
precise proof obligations are we can find the normal form of $\AF{∣ myTheory ∣}$
which turns out to be the type given here on the right of the $\_≡\_$ relation. 

\begin{code}

  resultType : ∣ myTheory ∣ ≡ 
             Σ ({x : Δᴵ} → (AgentURI ᶜ) x → ⊤)
               (λ x →
                 Σ ({x₁ : Δᴵ} → (PersonURI ᶜ) x₁ → (AgentURI ᶜ) x₁)
                   (λ x₁ →
                     Σ ((x₂ y : Δᴵ) → (KnowsURI ᴼᴾ) (x₂ , y) → (AgentURI ᶜ) y)
                       (λ x₂ →
                         Σ ((x₃ y : Δᴵ) → (KnowsURI ᴼᴾ) (x₃ , y) → (AgentURI ᶜ) x₃)
                           (λ x₃ → ⊤))))
  resultType = refl

\end{code}

These are then the obligations which we must fulfill in order to prove
that there is a model.  We show how this is done by filling it with a
term $\AF{testMyTheory}$ which Agda's type checker graciously admits
as filling the type.  We end up with a series of pairs, due to the
cartesian product formed by the translation of vectors into proof
obligations.  At each stage we have to produce a function which fills
the role of the predicate type which results from the description.  In
each case we write out the predicate explicitly $\AF{personIsAgent}$,
$\AF{agentRange}$ and $\AF{agentDomain}$.

\begin{code}

  testMyTheory : ∣ myTheory ∣
  testMyTheory = (λ x₁ → tt) ,
                 ((λ {x} p → personIsAgent x p) ,
                   ((λ x y p → agentRange x y p) ,
                     ((λ x y p → agentDomain x y p) , tt)))
               where personIsAgent : ∀ x → x ∈ PersonURI ᶜ → x ∈ AgentURI ᶜ
                     personIsAgent (C x) ()
                     personIsAgent (DP x) () 
                     personIsAgent (OP x) ()
                     personIsAgent (I JackURI) p = tt
                     personIsAgent (I JillURI) p = tt
                     agentRange : ∀ x y → (x , y) ∈ KnowsURI ᴼᴾ → y ∈ AgentURI ᶜ
                     agentRange (C x) (C x₁) ()
                     agentRange (C x) (DP x₁) ()
                     agentRange (C x) (OP x₁) ()
                     agentRange (C x) (I x₁) ()
                     agentRange (DP x) (C x₁) ()
                     agentRange (DP x) (DP x₁) ()
                     agentRange (DP x) (OP x₁) ()
                     agentRange (DP x) (I x₁) ()
                     agentRange (OP x) (C x₁) ()
                     agentRange (OP x) (DP x₁) ()
                     agentRange (OP x) (OP x₁) ()
                     agentRange (OP x) (I x₁) ()
                     agentRange (I x)  (C x₁) ()
                     agentRange (I x) (OP x₁) ()
                     agentRange (I x) (DP x₁) ()
                     agentRange (I x) (I x₁) x₂ with x | x₁
                     agentRange (I x) (I x₁) x₂ | JackURI | JackURI = tt
                     agentRange (I x) (I x₁) x₂ | JackURI | JillURI = tt
                     agentRange (I x) (I x₁) x₂ | JillURI | JackURI = tt
                     agentRange (I x) (I x₁) x₂ | JillURI | JillURI = tt 
                     agentDomain : ∀ x y → (x , y) ∈ KnowsURI ᴼᴾ → x ∈ AgentURI ᶜ
                     agentDomain (C x) y ()
                     agentDomain (DP x) y ()
                     agentDomain (OP x) y ()
                     agentDomain (I x) (C x₁) ()
                     agentDomain (I x) (DP x₁) ()
                     agentDomain (I x) (OP x₁) ()
                     agentDomain (I JackURI) (I y) p = tt
                     agentDomain (I JillURI) (I y) p = tt

\end{code}

\section{Conclusion and Future Work}

The contribution that we have made is to show how type theory provides
a natural framework for checking that some model really does satisfy
OWL's semantics.  This work can be used to make statements about the
relationships of various profiles and fragments.

It is technically possible to demonstrate that a given fragment is
decidable. This is done constructively by creating a function of the
following form:

\begin{code}

  postulate ⟦_⟧ : ∀ {n} → (theory : Theory n) → ∣ theory ∣ ⊎ ¬ ∣ theory ∣

\end{code}

The type of this function says that we can either find an inhabitant
of the theory, or the theory does not have any model whatseover.  This
is a very precise meaning of decidability that provides the model
itself or the proof that no model exists, both of which provide useful
information.  For full OWL such a thing is clearly impossible, so the
type of this function should actually be restricted such that
$\AB{theory}$ is drawn from the appropriate fragment to ensure
decidability.  In the future we hope to create a reasoner which does
just this.

Currently, while we provide semantics assuming the cardinality
functions, we do not show that the cardinality functions have any
meaning.  Indeed with the structure of the definitions presented one
could pass any cardinality function and it would be respected whether
it was associated with the number of individuals or not.  To avoid
this problem requires the use of finite sets and would complicate the
presentation somewhat, however we would like to provide an
implementation of this feature in the future.

It is useful to have formal semantics, but it is even better if the
formal semantics can be operationalised.  We have taken some first
modest steps towards operationalising the semantics of OWL such that
we can reason formally and mechanically using proof assistants.

\bibliographystyle{plain}
\bibliography{export.bib}

\end{document}
