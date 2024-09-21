\documentclass{report}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{fontspec}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb S}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb Q}}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal\top}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{⇒}{\ensuremath{\mathnormal\Rightarrow}}
\newunicodechar{⇐}{\ensuremath{\mathnormal\Leftarrow}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_\AgdaFontStyle{i}}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_\AgdaFontStyle{s}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_\AgdaFontStyle{o}}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^\AgdaFontStyle{r}}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^\AgdaFontStyle{u}}}}
\newunicodechar{₋}{\ensuremath{\mathnormal{_-}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal\uplus}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≢}{\ensuremath{\mathnormal\nequiv}}
\newunicodechar{≗}{\ensuremath{\mathnormal\circeq}}
\newunicodechar{∧}{\ensuremath{\mathnormal\land}}
\newunicodechar{≤}{\ensuremath{\mathnormal\leq}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{∸}{\ensuremath{\mathnormal\divdot}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{𝓁}{\ensuremath{\mathnormal{\mathcal l}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{χ}{\ensuremath{\mathnormal\chi}}
\newunicodechar{⊃}{\ensuremath{\mathnormal\supset}}
\newunicodechar{⊆}{\ensuremath{\mathnormal\subseteq}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{⊔}{\ensuremath{\mathnormal\sqcup}}
\newunicodechar{⊓}{\ensuremath{\mathnormal\sqcap}}
\newunicodechar{⟲}{\ensuremath{\mathnormal\circlearrowleft}}
\newunicodechar{𝓫}{\ensuremath{\mathnormal{\mathcal b}}}
\newunicodechar{𝓰}{\ensuremath{\mathnormal{\mathcal g}}}
\newunicodechar{𝓵}{\ensuremath{\mathnormal{\mathcal l}}}

\newfontface{\ayyplcihartai}{APL333}
\DeclareTextFontCommand{\ayypl}{\ayyplcihartai}
\newunicodechar{⌽}{\ensuremath{\ayypl ⌽}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\sds{\spacefactor\sfcode`.\ \space}

\newcommand\Xr[2]{\textrm{#1(#2)}}
\newcommand\datnyveicme\texttt

\title{le me'oi .Agda.\ velcki be la'o zoi.\ \Xr{shat}{1} .zoi.\ noi ke'a smimlu la'o zoi.\ \Xr{ed}{1} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\begin{abstract}
ni'o skicu bau la'oi .Agda.\ fe ko'a goi le milxe be le ka ce'u smimlu be la'o zoi.\ \Xr{ed}{1}\ .zoi.\ pe la'o zoi.\ Version 1 AT\&T UNIX\ .zoi.\ldots kei be'o poi ke'a selcme zoi zoi.\ \Xr{shat}{1}\ .zoi.\ldots ku'o je cu ciksi bau la'oi .Agda.\ le ctaipe be le su'u ko'a co'e ja mapti
\end{abstract}

\tableofcontents

\chapter{le vrici}

\begin{code}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --instance-search-depth=2 #-}

open import IO
  using (
    Main;
    run;
    IO
  )
open import Data.Fin
  as 𝔽
  using (
    Fin
  )
open import Data.Nat
  as ℕ
  using (
    suc;
    ℕ
  )
open import Data.Sum
  using (
    from-inj₁;
    map₁;
    inj₂;
    inj₁;
    _⊎_
  )
open import Function
  using (
    typeOf;
    _on_;
    _∘₂_;
    flip;
    _∋_;
    _$_;
    _∘_;
    id
  )
  renaming (
    _|>_ to _▹_
  )
open import Data.Bool
  as 𝔹
  using (
    false;
    Bool;
    T?
  )
  renaming (
    if_then_else_ to if
  )
open import Data.Char
  using (
    isDigit;
    Char
  )
open import Data.List
  as 𝕃
  using (
    List;
    _∷_;
    []
  )
  renaming (
    lookup to _!_;
    drop to _↓_;
    take to _↑_
  )
open import Data.Maybe
  using (
    decToMaybe;
    from-just;
    Is-just;
    nothing;
    Maybe;
    maybe;
    just
  )
open import Data.String
  as 𝕊
  using (
    unlines;
    String;
    lines
  )
open import Data.Product
  as Σ
  using (
    uncurry;
    proj₂;
    proj₁;
    _×_;
    _,_;
    ∃;
    Σ
  )
open import Relation.Unary
  using (
    Decidable;
    Pred;
    _⊆_
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    ¬_;
    no
  )
open import System.Environment
  using (
    getArgs
  )
open import Truthbrary.Data.Fin
  using (
    mink
  )
open import Truthbrary.Record.Eq
  using (
    _≡ᵇ_;
    _≟_;
    Eq
  )
open import Truthbrary.Record.SR
  using (
    readMaybe;
    Show;
    show
  )
open import Data.Unit.Polymorphic
  using (
    ⊤
  )
open import Truthbrary.Record.LLC
  using (
    liliList;
    length;
    _++_;
    _∈_;
    _∉_;
    cev;
    vec
  )
open import Truthbrary.Category.Monad
  using (
    _<=<_;
    _=<<_;
    _>>=_
  )
  renaming (
    map to mapₘ
  )
open import Relation.Nullary.Negation
  renaming (
    contradiction to _⇒⇐_
  )
open import Relation.Nullary.Decidable
  using (
    dec-yes
  )
open import Relation.Binary.PropositionalEquality
  using (
    module ≡-Reasoning;
    subst;
    cong;
    refl;
    _≗_;
    _≢_;
    _≡_;
    sym
  )

import IO.Finite
import Data.Fin.Show
  as 𝔽
import Agda.Builtin.IO
  as ABIO
import Agda.Builtin.Unit
  as ABU
import Data.Fin.Properties
  as DFP
import Data.Nat.Properties
  as DNP
import Data.List.Properties
  as DLP
import Data.Maybe.Instances
import Data.Maybe.Properties
  as DMP
import Data.List.Relation.Unary.All
  as 𝕃
  using (
    All
  )
import Data.Maybe.Relation.Unary.Any
  as DMA
\end{code}

\chapter{le me'oi .instance.\ pe le na se ciksi fo le velcki be le la'o zoi.\ \Xr{shat}{1}\ .zoi.}

\begin{code}
showF : {n : ℕ} → Show $ Fin n
showF = record {show = 𝔽.show}
\end{code}

\chapter{le se ctaipe}

\section{la'oi .\AgdaRecord{Buffer}.}
ni'o ciksi la'oi .\AgdaRecord{Buffer}.\ bau la .lojban.\ fo ma poi ke'a zabna

\begin{code}
record Buffer : Set
  where
  field
    datnyveicme : Maybe String
    lerpinste : List String
    cablerpinsle : Fin $ length lerpinste
    citri : List $ Σ (typeOf lerpinste) $ Fin ∘ length
    rejgaudatni : Maybe String
  F = typeOf cablerpinsle
  cninycitri = (lerpinste , cablerpinsle) ∷ citri
\end{code}

\subsection{tu'a la'oi .\D{Fin}.}
ni'o tu'a la'oi .\D{Fin}.\ nibli ko'a goi le su'u ro da poi ke'a ctaipe la'oi .\AgdaRecord{Buffer}.\ zo'u li su'o co'e ja nilzilcmi lo mu'oi zoi.\ \AgdaField{Buffer.lerpinste}\ .zoi.\ be da  .i pilno le co'e co ke na'e me mu'oi zoi.\ \F{if\AgdaUnderscore{}then\AgdaUnderscore{}else\AgdaUnderscore} .zoi.\ ki'u le su'u ko'a milxe ko'e goi le ka ce'u fegli la .varik.\ldots kei je ku'i cu mleca fi ko'e je le ka tu'a ce'u frili kei fe lo jalge be lo nu la'o zoi.\ \AgdaField{Buffer.cablerpinsle} .zoi.\ ctaipe la'o zoi.\ \Sym(\B x \Sym : \AgdaRecord{Buffer}\Sym) \Sym → \F{if} \Sym(\AgdaNumber 0 \OpF{ℕ.≤} \F{length} \Sym(\AgdaField{Buffer.lerpinste} \B x\Sym)\Sym) \Sym(\AgdaField{Buffer.F} \B x\Sym) \D ⊤\ .zoi.

\section{la'oi .\D{Cmd}.}
ni'o ctaipe ko'a goi la'o zoi.\ \D{Cmd} \B x\ .zoi.\ fa lo co'e be lo midnoi be fo la'o zoi.\ \Xr{ed}{1} .zoi.\ ja zo'e be'o poi ctaipe lo su'u tu'a ke'a racli

\newcommand\pavysumti[2]{ga je da du la'o zoi.\ \IC{#1} \B v\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ be'o bei #2}
\newcommand\cibysumti[2]{ga je da du la'o zoi.\ \IC{#1} \B v \B z \AgdaUnderscore{}\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ be'o bei lo me'oi .comma.\ bei lo sinxa be la'oi .\B z.\ be'o bei #2}
\newcommand\vonsumti[2]{ga je da du la'o zoi.\ \IC{#1} \B v \B x \B z\ \AgdaUnderscore{}\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ be'o bei lo me'oi .comma.\ bei lo sinxa be la'oi .\B x.\ be'o bei #2\ bei lo sinxa be la'oi .\B z.}
.i ro da poi ke'a ctaipe ko'a zo'u\ldots
\begin{itemize}
	\item ga jonai ga je da du la'oi .\IC{Sisti}.\ gi da mapti zo'oi .q.\ gi
	\item ga jonai ga je da du la'oi .\IC{Sisti!}.\ gi da mapti zo'oi .Q.\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Xruti}\ \B z.\ .zoi.\ gi da mapti zo'oi .u.\ldots je ku'i cu mapti le meirmoi be la'oi .\B z.\ bei fo la'o zoi.\ \AgdaField{Buffer.citri} \B x\ .zoi.\ gi
	\item ga jonai \pavysumti{Jmina}{zo'oi .a.}\ gi
	\item ga jonai \pavysumti{Jmini}{zo'oi .i.}\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Rejgau} \B v\ .zoi.\ gi da mapti lo konkatena be zo'oi .w.\ bei lo canlu lerfu bei la'oi .\B v.\ gi
	\item ga jonai \cibysumti{Vimcu}{zo'oi .d.} gi
	\item ga jonai \cibysumti{Basti}{zo'oi .c.} gi
	\item ga jonai \cibysumti{Cusku}{zo'oi .p.} gi
	\item ga jonai \cibysumti{Namcusku}{zo'oi .n.} gi
	\item ga je da du la'o zoi.\ \IC{Muvgau} \B v \B x \B z\ \AgdaUnderscore{}\ .zoi.\ gi\ldots
	\begin{itemize}
		\item ga jonai ga je la'oi .\B z.\ du la'o zoi.\ \IC{just}\ \B j\ .zoi.\ gi tu'a da rinka tu'a lo smimlu be lo jalge be lo nu mu'oi zoi.\ \Xr{ed}{1}\ .zoi.\ co'e lo konkatena be lo sinxa be lo sumji be la'oi .\B v\ .zoi.\ bei li pa be'o be'o bei lo me'oi .comma.\ bei lo sinxa be lo sumji be la'oi .\B x.\ bei li pa be'o be'o bei zo'oi .m.\ bei lo sinxa be lo sumji be la'oi .\B z.\ bei li pa gi
		\item ga je la'oi .\B z.\ du la'oi .\IC{nothing}.\ gi tu'a da rinka tu'a lo smimlu be lo jalge be lo nu mu'oi zoi.\ \Xr{ed}{1}\ .zoi.\ co'e lo konkatena be lo sinxa be lo sumji be la'oi .\B v\ .zoi.\ bei li pa be'o be'o bei lo me'oi .comma.\ bei lo sinxa be lo sumji be la'oi .\B x.\ bei li pa be'o be'o bei zo'oi .m0.
	\end{itemize}
\end{itemize}

\begin{code}
data Cmd (x : Buffer) : Set where
  Sisti : Cmd x
  Sisti! : Cmd x
  Jmina : Buffer.F x → Cmd x
  -- | ni'o la .varik. cu cnikansa lo se rigni
  -- be le klamburi
  Jmini : Buffer.F x → Cmd x
  Rejgau : String → Cmd x
  Vimcu : (a b : Buffer.F x) → a 𝔽.≤ b → Cmd x
  Namcusku : typeOf Vimcu
  Basti : typeOf Vimcu
  Cusku : typeOf Vimcu
  Muvgau : (a b : Buffer.F x)
         → Maybe $ Buffer.F x
         → a 𝔽.≤ b
         → Cmd x
  Xruti : Fin $ length $ Buffer.citri x → Cmd x
\end{code}

\section{la'oi .\D{Cmdᵢₒ}.}
ni'o ro da poi ke'a ctaipe la'o zoi.\ \D{Cmdᵢₒ} \B x\ .zoi.\ zo'u\ldots
\begin{itemize}
	\item ga jonai ga je da du la'o zoi.\ \IC{Rejgauᵢₒ} \B a \B b\ .zoi.\ gi tu'a da rinka lo nu rejgau benji la'oi .\B a.\ lo datnyvei poi ke'a selcme la'oi .\B b.\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Tciduᵢₒ} \B a \B b\ .zoi.\ gi\ldots
	\begin{itemize}
		\item ga jonai ga je la'oi .\B{b}.\ du la'oi .\IC{nothing}.\ gi tu'a da rinka tu'a lo ctaipe be la'oi .\AgdaRecord{Buffer}.\ be'o poi lo mu'oi zoi.\ \AgdaField{Buffer.lerpinste}\ .zoi.\ be ke'a cu konkatena fi lo mu'oi zoi.\ \AgdaField{Buffer.lerpinste}\ .zoi.\ be la'oi .\B{x}.\ fe ko'a goi lo'i ro lerpinsle pe lo datnyvei poi la'oi .\B{a}.\ cmene ke'a ku'o je poi lo mu'oi zoi.\ \AgdaField{Buffer.cablerpinsle}\ .zoi.\ be ke'a cu nilzilcmi ko'a gi
                \item ga je la'oi .\B{b}.\ du la'o zoi.\ \IC{just}\ \B n\ .zoi.\ gi tu'a da rinka tu'a lo ctaipe be la'oi .\AgdaRecord{Buffer}.\ be'o poi lo mu'oi zoi.\ \AgdaField{Buffer.lerpinste}\ .zoi.\ be ke'a cu konkatena la'o zoi.\ \IC{suc} \Sym(\F{𝔽.toℕ} \B n \OpF\Sym) \OpF ↑ \AgdaField{Buffer.lerpinste} \B x\ .zoi.\ ko'a la'o zoi.\ \IC{suc} \Sym(\F{𝔽.toℕ} \B n\Sym) \OpF ↓ \AgdaField{Buffer.lerpinste} \B x\ .zoi.\ je poi lo mu'oi zoi.\ \AgdaField{Buffer.cablerpinsle}\ .zoi.\ be ke'a cu\ldots mo gi
        \end{itemize}
	\item ga jonai ga je da du la'oi .\IC{Sistiᵢₒ}.\ gi tu'a da rinka lo nu co'e ja kajde ja cu sisti tu'a la'o zoi.\ \Xr{shat}{1}\ .zoi.\ gi
	\item ga jonai ga je da du la'oi .\IC{Sisti!ᵢₒ}.\ gi tu'a da rinka lo nu sisti tu'a la'o zoi.\ \Xr{shat}{1}\ .zoi.\ gi
	\item ga je da du la'o zoi.\ \IC{Skamiᵢₒ} \B x\ .zoi.\ gi tu'a da rinka lo nu .uniks.\ co'e la'oi .\B x.
\end{itemize}

\begin{code}
data Cmdᵢₒ (x : Buffer) : Set where
  Rejgauᵢₒ : String → String → Cmdᵢₒ x
  Tciduᵢₒ : String → Maybe $ Buffer.F x → Cmdᵢₒ x
  Skamiᵢₒ : String → Cmdᵢₒ x
  Sistiᵢₒ : Cmdᵢₒ x
  Sisti!ᵢₒ : Cmdᵢₒ x
\end{code}

\chapter{le mapti vrici je fancu}

\section{la'o zoi.\ \F{suc-dist-∸}\ .zoi.}
ni'o xu sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
suc-dist-∸ : {n m : ℕ}
           → n ℕ.≤ m
           → suc m ℕ.∸ n ≡ suc (m ℕ.∸ n)
suc-dist-∸ {0} ℕ.z≤n = refl
suc-dist-∸ {suc m} {suc n} (ℕ.s≤s s) = suc-dist-∸ s
\end{code}

\section{la'o zoi.\ \F{dec-just}\ .zoi.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi fo lo lojbo fe la'o zoi.\ \F{dec-just}\ .zoi.

\begin{code}
dec-just : ∀ {a p} → {A : Set a}
         → (P : Pred A p)
         → {x : A}
         → (P? : Dec $ P x)
         → (m : P x)
         → ∃ $ λ m → decToMaybe P? ≡ just m
dec-just _ = Σ.dmap id (cong decToMaybe) ∘₂ dec-yes
\end{code}

\section{la'o zoi.\ \F{dec-nothing}\ .zoi.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi fo lo lojbo fe la'o zoi.\ \F{dec-nothing}\ .zoi.

\begin{code}
dec-nothing : ∀ {a p} → {A : Set a}
            → (P : Pred A p)
            → {x : A}
            → (P? : Dec $ P x)
            → (m : ¬ P x)
            → decToMaybe P? ≡ nothing
dec-nothing _ P? m = begin
  decToMaybe P? ≡⟨ M ▹ proj₂ ▹ cong decToMaybe ⟩
  decToMaybe (no $ proj₁ M) ≡⟨ refl ⟩
  nothing ∎
  where
  M = Relation.Nullary.Decidable.dec-no P? m
  open ≡-Reasoning
\end{code}

\section{la \F{dekydu'i}}
ni'o xu sarcu fa lo nu la .varik.\ cu ciksi la \F{dekydu'i} bau la .lojban.

\begin{code}
dekydu'i : {x n : ℕ}
         → {mel : x ℕ.< n}
         → decToMaybe (x ℕ.<? n) ≡ just mel
dekydu'i {x} {n} {m} = begin
  decToMaybe (x ℕ.<? n) ≡⟨ DJ ▹ proj₂ ⟩
  just (proj₁ DJ) ≡⟨ iedek (proj₁ DJ) m ▹ cong just ⟩
  just m ∎
  where
  DJ = dec-just (ℕ._< n) (x ℕ.<? n) m
  iedek : {m n : ℕ} → (x z : m ℕ.< n) → x ≡ z
  iedek (ℕ.s≤s ℕ.z≤n) (ℕ.s≤s ℕ.z≤n) = refl
  iedek {suc m} {suc n} (ℕ.s≤s x) (ℕ.s≤s z) = I
    where
    I = iedek x z ▹ cong ℕ.s≤s
  open ≡-Reasoning
\end{code}

\section{la \F{zmadekydu'i}}

\begin{code}
zmadekydu'i : {x n : ℕ}
            → {m : x ℕ.≤ n}
            → decToMaybe (x ℕ.≤? n) ≡ just m
zmadekydu'i {x} {n} {m} = begin
  decToMaybe (x ℕ.≤? n) ≡⟨ proj₂ DJ ⟩
  just _ ≡⟨ DNP.≤-irrelevant _ m ▹ cong just ⟩
  just m ∎
  where
  DJ = dec-just (ℕ._≤ n) (_ ℕ.≤? n) m
  open ≡-Reasoning
\end{code}

\section{la'o zoi.\ \F{toList-dist}\ .zoi.}
ni'o xu sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
toList-dist : (x z : String)
            → 𝕊.toList (x ++ z) ≡ (_++_ on 𝕊.toList) x z
toList-dist = {!!}
\end{code}

\section{la'o zoi.\ \F{fromList-dist}\ .zoi.}
ni'o xu sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
fromList-dist : (x z : List Char)
              → ((_≡_ on λ f → f x z)
                  (𝕊.fromList ∘₂ _++_)
                  (_++_ on 𝕊.fromList))
fromList-dist = {!!}
\end{code}

\section{la'o zoi.\ \F{readMaybe∘show}\ .zoi.}
ni'o xu sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
readMaybe∘show : {n : ℕ} → readMaybe ∘ show ≗ just {A = Fin n}
readMaybe∘show = {!!}
\end{code}

\section{la'o zoi.\ \F{fromList∘toList}\ .zoi.}
ni'o xu sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
fromList∘toList : 𝕊.fromList ∘ 𝕊.toList ≗ id
fromList∘toList = {!!}
\end{code}

\section{la'o zoi.\ \F{toList∘fromChar}\ .zoi.}
ni'o xu sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
toList∘fromChar : 𝕊.toList ∘ 𝕊.fromChar ≗ (_∷ [])
toList∘fromChar = {!!}
\end{code}

\section{la .\F{romoitcar}.}
ni'o la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi fo lo lojbo

\begin{code}
romoitcar : (s : String)
          → (flip _≗_
              just
              (𝕃.last ∘ 𝕊.toList ∘ (s ++_) ∘ 𝕊.fromChar))
romoitcar s c = begin
  𝕃.last (𝕊.toList $ s ++ 𝕊.fromChar c) ≡⟨ refl ⟩
  _ ≡⟨ toList-dist s _ ▹ cong 𝕃.last ⟩
  𝕃.last (𝕊.toList s ++ 𝕊.toList (𝕊.fromChar c)) ≡⟨ refl ⟩
  _ ≡⟨ toList∘fromChar c ▹ cong (𝕃.last ∘ (𝕊.toList s ++_)) ⟩
  𝕃.last (𝕊.toList s ++ c ∷ []) ≡⟨ ⊃⌽-just c $ 𝕊.toList s ⟩
  just c ∎
  where
  open ≡-Reasoning
  ⊃⌽-just : ∀ {a} → {A : Set a}
          → (x : A)
          → (xs : List A)
          → 𝕃.last (xs ++ x ∷ []) ≡ just x
  ⊃⌽-just x [] = refl
  ⊃⌽-just x (_ ∷ zs) = ⊃⌽-just x zs ▹ subst (_≡ _) D
    where
    D = ⊃⌽∘x∷_≡⊃⌽ _ _ zs
      where
      ⊃⌽∘x∷_≡⊃⌽ : ∀ {a} → {A : Set a}
                → (x z : A)
                → (xs : List A)
                → ((_≡_ on 𝕃.last)
                    (xs ++ x ∷ [])
                    (z ∷ xs ++ x ∷ []))
      ⊃⌽∘x∷_≡⊃⌽ _ _ [] = refl
      ⊃⌽∘x∷_≡⊃⌽ _ _ (_ ∷ _) = refl
\end{code}

\section{la'oi .\F{readMaybe'}.}
ni'o ro da poi ke'a co'e zo'u\ldots
\begin{itemize}
	\item ga jonai ga je da du zoi zoi.\ \AgdaString{\$}\ .zoi.\ gi ko'a goi lo me'oi .\F{readMaybe'}.\ be da cu du la'o zoi.\ \IC{just} \IC{nothing}\ .zoi.\ gi\ldots
	\item ga jonai ga je su'o de poi ke'a ctaipe la'o zoi.\ \D{Fin} \B n\ .zoi.\ zo'u da du lo me'oi .\F{show}.\ be de gi ko'a me'oi .\IC{just}.\ lo se sinxa be da gi
	\item ko'a du la'oi .\IC{nothing}.
\end{itemize}

\begin{code}
readMaybe' : {n : ℕ} → String → Maybe $ Maybe $ Fin n
readMaybe' s = if (s ≡ᵇ "$") (just nothing) $ readMaybe s ▹ mapₘ just
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{readMaybe'}.\ mapti}

\begin{code}
module ReadMaybe'Veritas where
  open ≡-Reasoning

  jdini : {n : ℕ} → readMaybe' {n} "$" ≡ just nothing
  jdini = refl

  namcu : {n : ℕ}
        → readMaybe' {n} ∘ show ≗ just ∘ just
  namcu f = begin
    readMaybe' (show f) ≡⟨ refl ⟩
    if (show f ≡ᵇ "$") JN (RM $ show f) ≡⟨ refl ⟩
    _ ≡⟨ najdinis f ▹ cong (λ j → if j JN $ RM $ show f) ⟩
    if false JN (RM $ show f) ≡⟨ refl ⟩
    (readMaybe (show f) ▹ mapₘ just) ≡⟨ refl ⟩
    _ ≡⟨ readMaybe∘show f ▹ cong (mapₘ just) ⟩
    (just f ▹ mapₘ just) ≡⟨ refl ⟩
    just (just f) ∎
    where
    JN = just nothing
    RM = mapₘ just ∘ readMaybe
    najdinis : {n : ℕ} → (f : Fin n) → show f ≡ᵇ "$" ≡ false
    najdinis f with show f ≟ "$"
    ... | no j = refl
    ... | yes d = readMaybe∘show f ⇒⇐ subst (_≢ _) d' ¬J
      where
      d' = d ▹ sym ▹ cong readMaybe
      rM$≡N : {n : ℕ} → readMaybe "$" ≡ nothing {A = Fin n} 
      rM$≡N = {!!}
      N⇒¬J : ∀ {a} → {A : Set a}
           → {x : Maybe A}
           → x ≡ nothing
           → {z : A}
           → ¬_ $ x ≡ just z
      N⇒¬J refl ()
      ¬J = N⇒¬J rM$≡N

  justjust→namcu : {n : ℕ}
                 → (s : String)
                 → (f : Fin n)
                 → readMaybe' s ≡ just (just f)
                 → s ≡ show f
  justjust→namcu = {!!}

  justnothing→jdini : {n : ℕ}
                    → (s : String)
                    → readMaybe' {n} s ≡ just nothing
                    → s ≡ "$"
  justnothing→jdini s d with s ≟ "$"
  ... | yes d₁ = d₁
  ... | no n = d ⇒⇐ {!!}

  nada : {n : ℕ}
       → (s : String)
       → ¬_ $ s ≡ "$"
       → ¬_ $ Σ (Fin n) $ _≡_ s ∘ show
       → readMaybe' {n} s ≡ nothing
  nada s nj np = begin
    readMaybe' s ≡⟨ refl ⟩
    if (s ≡ᵇ "$") _ (jreadMaybe s) ≡⟨ ifnon nj ⟩
    jreadMaybe s ≡⟨ refl ⟩
    mapₘ just (readMaybe s) ≡⟨ norm s np ▹ cong (mapₘ just) ⟩
    mapₘ just nothing ≡⟨ refl ⟩
    nothing ∎
    where
    jreadMaybe = mapₘ just ∘ readMaybe
    norm : {n : ℕ}
         → (s : String)
         → ¬_ $ Σ (Fin n) $ _≡_ s ∘ show
         → readMaybe s ≡ nothing {A = Fin n}
    norm = λ s N → ¬J⇒N $ N ∘ J⇒Σ s
      where
      J⇒Σ : {n : ℕ}
          → (s : String)
          → ∃ (λ x → readMaybe s ≡ just {A = Fin n} x)
          → Σ (Fin n) $ _≡_ s ∘ show
      J⇒Σ = {!!}
      ¬J⇒N : ∀ {a} → {A : Set a}
           → {x : Maybe A}
           → ¬ (∃ $ λ z → x ≡ just z)
           → x ≡ nothing
      ¬J⇒N = {!!}
    ifnon : ∀ {a b} → {A : Set a} → {B : Set b}
          → ⦃ _ : Eq A ⦄
          → {d f : A}
          → {g j : B}
          → ¬_ $ d ≡ f
          → if (d ≡ᵇ f) g j ≡ j
    ifnon {d = d} {f = f} {g = g} {j = j} J = begin
      if (d ≡ᵇ f) g j ≡⟨ refl ⟩
      if (isYes $ d ≟ f) g j ≡⟨ isYes≗does (d ≟ f) ▹ cong i ⟩
      if (Dec.does $ d ≟ f) g j ≡⟨ dec-false (d ≟ f) J ▹ cong i ⟩
      j ∎
      where
      i = λ b → if b g j
      open Relation.Nullary.Decidable
        using (
          isYes≗does;
          dec-false;
          isYes
        )
\end{code}
  
\section{la'oi .\F{insert}.}
ni'o la .varik.\ na birti lo du'u ma kau zabna lo ka ce'u lojbo je cu velcki la'oi .\F{insert}.  .i la .varik.\ cu stidi lo nu lo na jimpe cu tcidu le velcki be le ctaipe be le su'u la'oi .\F{insert}.\ mapti

\begin{code}
insert : ∀ {a} → {A : Set a}
       → (x i : List A)
       → Maybe $ Fin $ length x
       → List A
insert x i n = (n' ↑ x) ++ i ++ (n' ↓ x)
  where
  n' = maybe 𝔽.toℕ (length x) n
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{insert}.\ mapti}

\begin{code}
module InsertVeritas where
  open ≡-Reasoning

  private
    lendrop : ∀ {a} → {A : Set a}
            → (x z : List A)
            → z ≡_ $ length x ↓_ $ x ++ z
    lendrop [] _ = refl
    lendrop (_ ∷ xs) = lendrop xs

    lenteik : ∀ {a} → {A : Set a}
            → (x z : List A)
            → x ≡_ $ length x ↑_ $ x ++ z
    lenteik [] _ = refl
    lenteik (x ∷ xs) z = lenteik xs z ▹ cong (x ∷_)

    finlen : ∀ {a} → {A : Set a}
           → (x : List A)
           → (n : Maybe $ Fin $ length x)
           → let n' = maybe 𝔽.toℕ (length x) n in
             n' ≡ length (n' ↑ x)
    finlen [] nothing = refl
    finlen (_ ∷ xs) (just 𝔽.zero) = refl
    finlen (_ ∷ xs) nothing = finlen xs nothing ▹ cong suc
    finlen (_ ∷ xs) (just (𝔽.suc n)) = finlen xs (just n) ▹ cong suc
       
  lynyrd : ∀ {a} → {A : Set a}
         → (x i : List A)
         → (n : Maybe $ Fin $ length x)
         → length x ℕ.+ length i ≡ length (insert x i n)
  lynyrd x i n = sym $ begin
    L (insert x i n)
      ≡⟨ refl ⟩
    L ((n' ↑ x) ++ i ++ (n' ↓ x))
      ≡⟨ DLP.length-++ $ n' ↑ x ⟩
    L (n' ↑ x) ℕ.+ L (i ++ (n' ↓ x))
      ≡⟨ DLP.length-++ i ▹ cong (ℕ._+_ _) ⟩
    L (n' ↑ x) ℕ.+ (L i ℕ.+ L (n' ↓ x))
      ≡⟨ DNP.+-comm (L i) _ ▹ cong (ℕ._+_ $ L $ n' ↑ x) ⟩
    L (n' ↑ x) ℕ.+ (L (n' ↓ x) ℕ.+ L i)
      ≡⟨ DNP.+-assoc (L $ n' ↑ x) _ _ ▹ sym ⟩
    L (n' ↑ x) ℕ.+ L (n' ↓ x) ℕ.+ L i
      ≡⟨ DLP.length-++ (n' ↑ x) ▹ sym ▹ cong (ℕ._+ L i) ⟩
    L (n' ↑ x ++ n' ↓ x) ℕ.+ L i
      ≡⟨ DLP.take++drop n' x ▹ cong ((ℕ._+ L i) ∘ L) ⟩
    L x ℕ.+ L i ∎
    where
    L = length
    n' = maybe 𝔽.toℕ (L x) n

  pamois : ∀ {a} → {A : Set a}
         → (x i : List A)
         → (n : Maybe $ Fin $ length x)
         → let n' = maybe 𝔽.toℕ (length x) n in
           ((_≡_ on (n' ↑_))
             x
             (insert x i n))
  pamois x i n = sym $ begin
    n' ↑ insert x i n ≡⟨ refl ⟩
    n' ↑ ((n' ↑ x) ++ i ++ (n' ↓ x)) ≡⟨ refl ⟩
    _ ≡⟨ finlen x n ▹ cong (_↑ ((n' ↑ x) ++ i ++ (n' ↓ x))) ⟩
    length (n' ↑ x) ↑ ((n' ↑ x) ++ i ++ (n' ↓ x)) ≡⟨ refl ⟩
    _ ≡⟨ lenteik (n' ↑ x) _ ▹ sym ⟩
    n' ↑ x ∎
    where
    n' = maybe 𝔽.toℕ (length x) n

  remois : ∀ {a} → {A : Set a}
         → (x i : List A)
         → (n : Maybe $ Fin $ length x)
         → let n' = maybe 𝔽.toℕ (length x) n in
           i ≡_ $ length i ↑_ $ n' ↓ insert x i n
  remois x i n = sym $ begin
    L i ↑ (n' ↓ insert x i n) ≡⟨ refl ⟩
    L i ↑ (n' ↓_ $ x₁ ++ i ++ x₂) ≡⟨ refl ⟩
    _ ≡⟨ finlen x n ▹ cong (L i ↑_ ∘ _↓ (x₁ ++ i ++ x₂)) ⟩
    L i ↑ (L x₁ ↓_ $ x₁ ++ i ++ x₂) ≡⟨ refl ⟩
    _ ≡⟨ lendrop x₁ _ ▹ sym ▹ cong (_ ↑_) ⟩
    L i ↑ (i ++ x₂) ≡⟨ lenteik i x₂ ▹ sym ⟩
    i ∎
    where
    L = length
    n' = maybe 𝔽.toℕ (L x) n
    x₁ = n' ↑ x
    x₂ = n' ↓ x

  romois : ∀ {a} → {A : Set a}
         → (x i : List A)
         → (n : Maybe $ Fin $ length x)
         → let n' = maybe 𝔽.toℕ (length x) n in
           n' ↓ x ≡ (n' ℕ.+ length i) ↓ insert x i n
  romois x i n = sym $ begin
    (n' ℕ.+ 𝓁 i) ↓ insert x i n
      ≡⟨ refl ⟩
    (n' ℕ.+ 𝓁 i) ↓ (x₁ ++ i ++ x₂)
      ≡⟨ finlen x n ▹ cong (λ n → (n ℕ.+ 𝓁 i) ↓ K) ⟩
    (𝓁 (n' ↑ x) ℕ.+ 𝓁 i) ↓ (x₁ ++ i ++ x₂)
      ≡⟨ refl ⟩
    (𝓁 x₁ ℕ.+ 𝓁 i) ↓ (x₁ ++ i ++ x₂)
      ≡⟨ DLP.length-++ x₁ ▹ sym ▹ cong (_↓ K) ⟩
    𝓁 (x₁ ++ i) ↓ (x₁ ++ i ++ x₂)
      ≡⟨ DLP.++-assoc x₁ i x₂ ▹ sym ▹ cong (_↓_ $ 𝓁 $ x₁ ++ i) ⟩
    𝓁 (x₁ ++ i) ↓ ((x₁ ++ i) ++ x₂)
      ≡⟨ dropydus $ x₁ ++ i ⟩
    x₂
      ≡⟨ refl ⟩
    n' ↓ x ∎
    where
    𝓁 = length
    n' = maybe 𝔽.toℕ (𝓁 x) n
    x₁ = n' ↑ x
    x₂ = n' ↓ x
    K = x₁ ++ i ++ x₂
    dropydus : ∀ {a} → {A : Set a}
             → (x : List A)
             → {z : List A}
             → length x ↓ (x ++ z) ≡ z
    dropydus = λ {[] → refl; (_ ∷ xs) → dropydus xs}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{},ₘ\AgdaUnderscore}\ .zoi.}
ni'o xu sarcu fa lo nu ciksi bau la .lojban.

\begin{code}
_,ₘ_ : ∀ {a} → {A B : Set a}
     → Maybe A → Maybe B → Maybe $ A × B
_,ₘ_ = Data.Maybe.ap ∘ mapₘ _,_
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{\AgdaUnderscore{},ₘ\AgdaUnderscore}\ .zoi.\ mapti}

\begin{code}
module _,ₘ_Veritas where
  jj : ∀ {a} → {A B : Set a}
     → (x : A)
     → (z : B)
     → (just x ,ₘ just z) ≡ just (x , z)
  jj _ _ = refl

  n₁ : ∀ {a} → {A B : Set a}
      → (z : Maybe B)
      → (nothing {A = A} ,ₘ z) ≡ nothing
  n₁ _ = refl

  n₂ : ∀ {a} → {A B : Set a}
      → (x : Maybe A)
      → (x ,ₘ nothing {A = B}) ≡ nothing
  n₂ = λ {nothing → refl; (just _) → refl}
\end{code}

\section{la'oi .\F{fromℕ?}.}
ni'o ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{fromℕ?}\ \B x\ .zoi.\ gi la'o zoi.\ \F{mapₘ} \F{𝔽.toℕ} \OpF \$ \F{fromℕ?}\ \B x\ .zoi.\ me'oi .\IC{just}.\ zo'e poi la'oi .\B x.\ mu'oi zoi.\ \F{𝔽.toℕ}\ .zoi.\ ke'a

\begin{code}
fromℕ? : {n : ℕ} → ℕ → Maybe $ Fin n
fromℕ? = mapₘ 𝔽.fromℕ< ∘ decToMaybe ∘ (ℕ._<? _)
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{fromℕ?}.\ mapti}

\begin{code}
module fromℕ?Veritas where
  open ≡-Reasoning

  jus : {n : ℕ}
      → (x : ℕ)
      → x ℕ.< n
      → just x ≡ mapₘ 𝔽.toℕ (fromℕ? {n} x)
  jus {n} x m = sym $ begin
    mapₘ 𝔽.toℕ (fromℕ? {n} x) ≡⟨ refl ⟩
    mapₘ 𝔽.toℕ (mapₘ 𝔽.fromℕ< c?) ≡⟨ mapmapi c? ⟩
    mapₘ id' c? ≡⟨ dekydu'i ▹ cong (mapₘ id') ⟩
    mapₘ id' (just m) ≡⟨ refl ⟩
    just (id' m) ≡⟨ DFP.toℕ-fromℕ< _ ▹ cong just ⟩
    just x ∎
    where
    id' = 𝔽.toℕ ∘ 𝔽.fromℕ<
    c? : {x : ℕ} → Maybe $ x ℕ.< n
    c? {x} = decToMaybe $ (ℕ._<? _) x
    mapmapi = sym ∘ DMP.map-compose

  nada : {n : ℕ}
       → (x : ℕ)
       → ¬_ $ x ℕ.< n
       → nothing ≡ mapₘ 𝔽.toℕ (fromℕ? {n} x)
  nada {n} x J = sym $ begin
    mapₘ 𝔽.toℕ (fromℕ? {n} x) ≡⟨ refl ⟩
    mapₘ 𝔽.toℕ (mapₘ 𝔽.fromℕ< $ d2m $ x ℕ.<? n) ≡⟨ MC ▹ sym ⟩
    mapₘ (𝔽.toℕ ∘ 𝔽.fromℕ<) (d2m $ x ℕ.<? n) ≡⟨ refl ⟩
    _ ≡⟨ DN ▹ cong (mapₘ $ 𝔽.toℕ ∘ 𝔽.fromℕ<) ⟩
    nothing ∎
    where
    d2m = decToMaybe
    MC = DMP.map-compose $ d2m $ x ℕ.<? n
    DN = dec-nothing (ℕ._< _) (x ℕ.<? n) J

  fromℕ?∘toℕ : {n : ℕ} → just ≗ fromℕ? ∘ 𝔽.toℕ {n}
  fromℕ?∘toℕ {n} f = sym $ begin
    fromℕ? (𝔽.toℕ f) ≡⟨ refl ⟩
    mapₘ 𝔽.fromℕ< (decToMaybe $ (ℕ._<? _) $ 𝔽.toℕ f) ≡⟨ refl ⟩
    _ ≡⟨ DY ▹ proj₂ ▹ cong (mapₘ 𝔽.fromℕ< ∘ decToMaybe) ⟩
    mapₘ (𝔽.fromℕ<) (just $ proj₁ DY) ≡⟨ refl ⟩
    just (𝔽.fromℕ< $ proj₁ DY) ≡⟨ refl ⟩
    _ ≡⟨ DFP.fromℕ<-toℕ _ (proj₁ DY) ▹ cong just ⟩
    just f ∎
    where
    DY = dec-yes (_ ℕ.<? _) $ DFP.toℕ<n f
\end{code}

\section{la'oi .\F{degjygirzu}.}
ni'o la .varik.\ na birti lo du'u ciksi bau la .lojban.\ fe la \F{degjygirzu}\ fo ma kau poi ke'a zabna

\begin{code}
degjygirzu : String → List String
degjygirzu = 𝕊.wordsBy $ T? ∘ 𝔹.not ∘ isDigit
\end{code}

\subsection{le ctaipe be le su'u la \F{degjygirzu}\ cu mapti}

\begin{code}
module DegjygirzuVeritas where
  open ≡-Reasoning

  pav : degjygirzu ∘ show ≗ (_∷ []) ∘ show {A = ℕ}
  pav n = begin
    degjygirzu (show n) ≡⟨ refl ⟩
    𝕃.map 𝕊.fromList (d $ 𝕊.toList $ show n) ≡⟨ refl ⟩
    mL (d $ show' n) ≡⟨ didus n ▹ cong mL ⟩
    mL (show' n ∷ []) ≡⟨ fL∘tL (show n) ▹ cong (_∷ []) ⟩
    show n ∷ [] ∎
    where
    fL∘tL = fromList∘toList
    mL = 𝕃.map 𝕊.fromList
    show' = 𝕊.toList ∘ show
    d = 𝕃.wordsBy $ T? ∘ 𝔹.not ∘ isDigit
    didus : d ∘ show' ≗ (_∷ []) ∘ show'
    didus = {!!}

  rybic : (s : String)
        → (c : Char)
        → false ≡ isDigit c
        → degjygirzu s ≡ degjygirzu (𝕊.fromChar c ++ s)
  rybic s c j = sym $ begin
    degjygirzu (𝕊.fromChar c ++ s) ≡⟨ refl ⟩
    degjygirzu (fC c ++ s) ≡⟨ refl ⟩
    d' (tL $ fC c ++ s) ≡⟨ toList-dist (fC c) s ▹ cong d' ⟩
    d' (tL (fC c) ++ tL s) ≡⟨ tilfic c ▹ cong (d' ∘ (_++ tL s)) ⟩
    d' ((c ∷ []) ++ tL s) ≡⟨ refl ⟩
    d' (c ∷ tL s) ≡⟨ refl ⟩
    𝕃.map fL (𝕃.wordsBy (F? ∘ isDigit) $ c ∷ tL s) ≡⟨ refl ⟩
    _ ≡⟨ uobis c (tL s) (fineg j) ▹ cong (𝕃.map fL) ⟩
    𝕃.map fL (𝕃.wordsBy (F? ∘ isDigit) $ tL s) ≡⟨ refl ⟩
    degjygirzu s ∎
    where
    tL = 𝕊.toList
    fL = 𝕊.fromList
    fC = 𝕊.fromChar
    F? = T? ∘ 𝔹.not
    -- | .i cicna finpe
    tilfic : tL ∘ fC ≗ 𝕃.[_]
    tilfic = toList∘fromChar
    d' = 𝕃.map fL ∘ (𝕃.wordsBy $ F? ∘ isDigit)
    fineg : _≡_ false ⊆ 𝔹.T ∘ 𝔹.not
    fineg refl = _
    uobis : ∀ {a p} → {A : Set a}
          → {P : Pred A p}
          → {P? : Decidable P}
          → (x : A)
          → (xs : List A)
          → P x
          → 𝕃.wordsBy P? (x ∷ xs) ≡ 𝕃.wordsBy P? xs
    uobis = {!!}

  rel : (s : String)
      → (t : ℕ)
      → (c : Char)
      → false ≡ isDigit c
      → (_≡_
          (show t ∷ degjygirzu s)
          (degjygirzu $ show t ++ 𝕊.fromChar c ++ s))
  rel s t c j = sym $ begin
    d (show t ++ 𝕊.fromChar c ++ s) ≡⟨ dc (show t) _ ⟩
    d (show t) ++ d (𝕊.fromChar c ++ s) ≡⟨ refl ⟩
    _ ≡⟨ rybic s c j ▹ sym ▹ cong (_ ++_) ⟩
    d (show t) ++ d s ≡⟨ pav t ▹ cong (_++ d s) ⟩
    (show t ∷ []) ++ d s ≡⟨ refl ⟩
    show t ∷ d s ∎
    where
    d = degjygirzu
    tL = 𝕊.toList
    fL = 𝕊.fromList
    d' = 𝕃.map fL ∘_ $ 𝕃.wordsBy $ T? ∘ 𝔹.not ∘ isDigit
    fL∘tL = fromList∘toList
    dc : {c : Char}
       → (s₁ s₂ : String)
       → (_≡_
           (d $ s₁ ++ 𝕊.fromChar c ++ s₂)
           (d s₁ ++ d (𝕊.fromChar c ++ s₂)))
    dc = {!!}
\end{code}

\section{la'oi .\F{pamoinamcu}.}
ni'o ro da xi pa poi ke'a na'e degji lerfu zo'u ro da xi re poi ke'a ctaipe la'oi .\AgdaPostulate{String}.\ zo'u ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{pamoinamcu} \B x\ .zoi.\ gi su'o de poi ke'a kacna'u zo'u ga je la'oi .\B x.\ konkatena lo sinxa be de bei de xi pa bei de xi re gi ko'a de me'oi .\IC{just}.

\begin{code}
pamoinamcu : String → Maybe ℕ
pamoinamcu = readMaybe <=< 𝕃.head ∘ degjygirzu
\end{code}

\subsection{le ctaipe be le su'u mapti fa la'oi .\F{pamoinamcu}.}

\begin{code}
module PamoinamcuVeritas where
  open ≡-Reasoning

  non : readMaybe ∘ show ≗ just
      → id ≗ 𝕊.fromList ∘ 𝕊.toList
      → just ≗ pamoinamcu ∘ show
  non rimco fL∘tL n = sym $ begin
    pamoinamcu (show n) ≡⟨ refl ⟩
    𝕃.head (s $ show n) >>= readMaybe ≡⟨ refl ⟩
    g (s $ show n) ≡⟨ DegjygirzuVeritas.pav n ▹ cong g ⟩
    g (show n ∷ []) ≡⟨ refl ⟩
    𝕃.head (show n ∷ []) >>= readMaybe ≡⟨ refl ⟩
    readMaybe (show n) ≡⟨ rimco n ⟩
    just n ∎
    where
    g = readMaybe <=< 𝕃.head
    s = degjygirzu

  pav : ((n : ℕ) → readMaybe (show n) ≡ just n)
      → (n : ℕ)
      → (c : Char)
      → (s : String)
      → false ≡ isDigit c
      → just n ≡ pamoinamcu (show n ++ 𝕊.fromChar c ++ s)
  pav rimco n c t j = sym $ begin
   pamoinamcu (show n ++ c' ++ t) ≡⟨ refl ⟩
   𝕃.head (d $ show n ++ c' ++ t) >>= readMaybe ≡⟨ refl ⟩
   g (d $ show n ++ c' ++ t) ≡⟨ dvr t n c j ▹ sym ▹ cong g ⟩
   g (show n ∷ d (c' ++ t)) ≡⟨ refl ⟩
   readMaybe =<< 𝕃.head (show n ∷ d (c' ++ t)) ≡⟨ refl ⟩
   readMaybe (show n) ≡⟨ rimco n ⟩
   just n ∎
   where
   dvr = DegjygirzuVeritas.rel
   c' = 𝕊.fromChar c
   g = readMaybe <=< 𝕃.head
   d = degjygirzu
\end{code}

\section{la'oi .\F{romoivimcu}.}
ni'o la .varik.\ na birti lo du'u ciksi la'oi .\F{romoivimcu}.\ fo ma kau poi ke'a zabna je cu te gerna la .lojban.

\begin{code}
romoivimcu : String → String
romoivimcu = S $ λ L → _↑ L $ 𝕃.length L ℕ.∸ 1
  where
  S = λ f → 𝕊.fromList ∘ f ∘ 𝕊.toList
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{romoivimcu}.\ mapti}

\begin{code}
module RomoivimcuVeritas where
  open ≡-Reasoning

  konkydus : (x : String)
           → let -1↑x = 𝕊.fromList $ (length x ℕ.∸ 1) ↓ 𝕊.toList x in
             x ≡ romoivimcu x ++ -1↑x
  konkydus x = sym $ begin
    romoivimcu x ++ 𝕊.fromList -1↑x ≡⟨ refl ⟩
    fL (_↑ x' $ length x' ℕ.∸ 1) ++ 𝕊.fromList -1↑x ≡⟨ refl ⟩
    fL -1↓x' ++ fL -1↑x ≡⟨ fromList-dist -1↓x' -1↑x ▹ sym ⟩
    fL (-1↓x' ++ -1↑x) ≡⟨ refl ⟩
    fL x'' ≡⟨ DLP.take++drop (length x' ℕ.∸ 1) x' ▹ cong fL ⟩
    fL x' ≡⟨ fromList∘toList x ⟩
    x ∎
    where
    x' = 𝕊.toList x
    fL = 𝕊.fromList
    -1↑x = _↓ x' $ length x' ℕ.∸ 1
    -1↓x' = _↑ x' $ length x' ℕ.∸ 1
    x'' = -1↓x' ++ -1↑x

  vimcykonkydus : (s : String)
              → (c : Char)
              → romoivimcu (s ++ 𝕊.fromChar c) ≡ s
  vimcykonkydus s c = begin
    romoivimcu (s ++ fC c) ≡⟨ refl ⟩
    S -1↓_ (s ++ fC c) ≡⟨ refl ⟩
    fL (-1↓_ $ tL $ s ++ fC c) ≡⟨ refl ⟩
    _ ≡⟨ toList-dist s (fC c) ▹ cong (fL ∘ -1↓_) ⟩
    fL (-1↓_ $ tL s ++ tL (fC c)) ≡⟨ refl ⟩
    _ ≡⟨ toList∘fromChar c ▹ cong (fL ∘ -1↓_ ∘ (tL s ++_)) ⟩
    fL (-1↓_ $ tL s ++ c ∷ []) ≡⟨ -1↓_∘konk≡id (tL s) c ▹ cong fL ⟩
    fL (tL s) ≡⟨ fL∘tL≡id s ⟩
    s ∎
    where
    tL = 𝕊.toList
    fC = 𝕊.fromChar
    fL = 𝕊.fromList
    -1↓_ : ∀ {a} → {A : Set a} → List A → List A
    -1↓_ = λ L → _↑ L $ length L ℕ.∸ 1
    S = λ f → 𝕊.fromList ∘ f ∘ 𝕊.toList
    fL∘tL≡id : fL ∘ tL ≗ id
    fL∘tL≡id = {!!}
    -1↓_∘konk≡id : ∀ {a} → {A : Set a}
                 → (xs : List A)
                 → (x : A)
                 → -1↓_ (xs ++ x ∷ []) ≡ xs
    -1↓_∘konk≡id [] _ = refl
    -1↓_∘konk≡id x@(_ ∷ _) e = begin
      -1↓_ (x ++ e ∷ []) ≡⟨ refl ⟩
      (length (x ++ e ∷ []) ℕ.∸ 1) ↑ (x ++ e ∷ []) ≡⟨ refl ⟩
      _ ≡⟨ l[x++e∷[]]∸1≡l[x] x e ▹ cong (_↑ (x ++ e ∷ [])) ⟩
      length x ↑ (x ++ e ∷ []) ≡⟨ l[x]↑[x++z]≡x x $ e ∷ [] ⟩
      x ∎
      where
      l[x++e∷[]]∸1≡l[x] : ∀ {a} → {A : Set a}
                       → (x : List A)
                       → (e : A)
                       → length (x ++ e ∷ []) ℕ.∸ 1 ≡ length x
      l[x++e∷[]]∸1≡l[x] [] e = refl
      l[x++e∷[]]∸1≡l[x] (x ∷ xs) e = begin
        length ((x ∷ xs) ++ e ∷ []) ℕ.∸ 1 ≡⟨ refl ⟩
        _ ≡⟨ D ∋ {!!} ▹ cong (ℕ._∸ 1) ⟩
        length (e ∷ x ∷ xs) ℕ.∸ 1 ≡⟨ refl ⟩
        length (x ∷ xs) ∎
        where
        D = length ((x ∷ xs) ++ e ∷ []) ≡ length (e ∷ x ∷ xs)
      l[x]↑[x++z]≡x : ∀ {a} → {A : Set a}
                    → (x z : List A)
                    → length x ↑ (x ++ z) ≡ x
      l[x]↑[x++z]≡x [] z = refl
      l[x]↑[x++z]≡x (x ∷ xs) = cong (x ∷_) ∘ l[x]↑[x++z]≡x xs

  kunti : romoivimcu "" ≡ ""
  kunti = refl
\end{code}

\section{la'oi .\F{orsygenturfa'i}.}
ni'o ro da poi ke'a ctaipe ko'a goi la'o zoi.\ \D{Fin} \B n\ .zoi.\ zo'u ro de poi ke'a ctaipe ko'a zo'u ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{orsygenturfa'i} \B s\ .zoi.\ gi ga je da dubjavme'a de gi ga je ko'a me'oi .\IC{just}.\ lo .orsi be li re bei lo .orsi be li re bei da bei de be'o bei lo ctaipe be lo su'u da dubjavme'a de gi la'oi .\B s.\ konkatena lo sinxa be da lo me'oi .comma.\ lo sinxa be de

\begin{code}
module Orsygenturfa'i where
  ps : {n : ℕ} → List Char → Maybe $ Fin n
  ps = fromℕ? <=< (readMaybe ∘ 𝕊.fromList)

  spit : String → List $ List Char
  spit = 𝕃.wordsBy (_≟ ',') ∘ 𝕊.toList

  pork : {n : ℕ}
       → List $ Maybe $ Fin n
       → Maybe $ ∃ $ uncurry $ 𝔽._≤_ {n}
  pork (just a ∷ just b ∷ []) = mapₘ (_ ,_) $ decToMaybe $ a 𝔽.≤? b
  pork _ = nothing

  orsygenturfa'i : {n : ℕ}
                 → String
                 → Maybe $ ∃ $ uncurry $ 𝔽._≤_ {n}
  orsygenturfa'i = pork ∘ 𝕃.map ps ∘ spit

open Orsygenturfa'i
  using (
    orsygenturfa'i
  )
\end{code}

\subsection{le krinu be le me'oi .\AgdaKeyword{module}.\ co'e}
ni'o pilno ko'a goi le me'oi .\AgdaKeyword{module}.\ co'e ki'u le su'u tu'a ko'a filri'a lo nu ciksi lo ctaipe be le su'u mapti  .i la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi lo steci be la'oi .\F{orgenturfa'i}.\ jenai zo'e bau la .lojban.

\subsection{le ctaipe be le su'u la'oi .\F{orsygenturfa'i}.\ mapti}

\begin{code}
module Orsygenturfa'iVeritas where
  open Orsygenturfa'i

  module Spit where
    non : spit "" ≡ []
    non = refl

    pav : (x : String)
        → ',' ∉ 𝕊.toList x
        → Σ Char $ _∈ 𝕊.toList x
        → spit x ≡ 𝕊.toList x ∷ []
    pav x nin inn = begin
      spit x ≡⟨ refl ⟩
      𝕃.wordsBy (_≟ ',') (𝕊.toList x) ≡⟨ {!!} ⟩
      𝕊.toList x ∷ [] ∎
      where
      ninwords : ∀ {a p} → {A : Set a}
               → {P : Pred A p}
               → (P? : Decidable P)
               → (x : A)
               → (xs : List A)
               → 𝕃.All (¬_ ∘ P) $ x ∷ xs
               → 𝕃.wordsBy P? (x ∷ xs) ≡ (x ∷ xs) ∷ []
      ninwords P? x [] (d 𝕃.All.∷ 𝕃.All.[]) = {!!}
      ninwords P? x (z ∷ zs) L = {!!}
      ninal : ∀ {a} → {A : Set a}
            → ⦃ _ : Eq A ⦄
            → {x : A}
            → {xs : List A}
            → x ∉ xs
            → 𝕃.All (_≢ x) xs
      ninal {xs = []} _ = 𝕃.All.[]
      ninal {xs = z ∷ zs} n = ∉⇒≢ n 𝕃.All.∷ ninal (∉⇒∉₋₁ {xs = zs} n)
        where
        ∉⇒≢ : ∀ {a} → {A : Set a}
            → ⦃ _ : Eq A ⦄
            → {e x : A}
            → {xs : List A}
            → e ∉ (x ∷ xs)
            → x ≢ e
        ∉⇒≢ {e = e} {x} {xs} nin with x ≟ _
        ... | yes d = ≡⇒∈ _ _ xs (sym d) ⇒⇐ ∉⇒¬∈ _ (x ∷ xs) nin
          where
          ≡⇒∈ : ∀ {a} → {A : Set a}
              → ⦃ _ : Eq A ⦄
              → (e x : A)
              → (xs : List A)
              → e ≡ x
              → e ∈_ $ x ∷ xs
          ≡⇒∈ = {!!}
          ∉⇒¬∈ : ∀ {a} → {A : Set a}
               → ⦃ _ : Eq A ⦄
               → (x : A)
               → (xs : List A)
               → x ∉ xs
               → ¬_ $ x ∈ xs
          ∉⇒¬∈ x [] nin = λ ()
          ∉⇒¬∈ e (x ∷ xs) nin = {!!}
        ... | no j = j
        ∉⇒∉₋₁ : ∀ {a} → {A : Set a}
              → ⦃ _ : Eq A ⦄
              → {e x : A}
              → {xs : List A}
              → e ∉_ $ x ∷ xs
              → e ∉ xs
        ∉⇒∉₋₁ {xs = []} _ = refl
        ∉⇒∉₋₁ {e = e} {xs = z ∷ zs} = f[x∷xs]≡[]⇒f[xs]≡[] $ e ≟_
          where
          f[x∷xs]≡[]⇒f[xs]≡[] : ∀ {a p} → {A : Set a}
                              → {x : A}
                              → {xs : List A}
                              → {P : Pred A p}
                              → (P? : Decidable P)
                              → 0 ≡_ $ length $ 𝕃.filter P? $ x ∷ xs
                              → 0 ≡_ $ length $ 𝕃.filter P? xs
          f[x∷xs]≡[]⇒f[xs]≡[] = {!!}
      open ≡-Reasoning

    du : (x z : String)
       → ',' ∉ 𝕊.toList x
       → ',' ∉ 𝕊.toList z
       → Σ Char $ _∈ x
       → Σ Char $ _∈ z
       → spit (x ++ "," ++ z) ≡ 𝕊.toList x ∷ 𝕊.toList z ∷ []
    du x z inx inz innx innz = begin
      spit (x ++ "," ++ z) ≡⟨ refl ⟩
      w (tL $ x ++ "," ++ z) ≡⟨ toList-dist x ("," ++ z) ▹ cong w ⟩
      w (tL x ++ tL ("," ++ z)) ≡⟨ refl ⟩
      _ ≡⟨ toList-dist "," z ▹ cong (w ∘ _++_ (tL x)) ⟩
      w (tL x ++ tL "," ++ tL z) ≡⟨ refl ⟩
      w (tL x ++ ',' ∷ tL z) ≡⟨ uit _ (tL x) _ (F inx) (F inz) _ refl ⟩
      w (tL x) ++ w (tL z) ≡⟨ {!!} ⟩
      (tL x ∷ []) ++ w (tL z) ≡⟨ refl ⟩
      _ ≡⟨ (w (tL z) ≡ (tL z ∷ [])) ∋ {!!} ▹ cong ((tL x ∷ []) ++_) ⟩
      (tL x ∷ []) ++ (tL z ∷ []) ≡⟨ refl ⟩
      tL x ∷ tL z ∷ [] ∎
      where
      tL = 𝕊.toList
      w = 𝕃.wordsBy $ _≟ ','
      F : ∀ {a} → {A : Set a}
        → ⦃ _ : Eq A ⦄
        → {e : A}
        → {x : List A}
        → e ∉ x
        → 𝕃.All (_≢ e) x
      F = {!!}
      uit : ∀ {a p} → {A : Set a} → {P : Pred A p}
          → (P? : Decidable P)
          → (x z : List A)
          → 𝕃.All (¬_ ∘ P) x
          → 𝕃.All (¬_ ∘ P) z
          → (e : A)
          → P e
          → (_≡_
              (𝕃.wordsBy P? $ x ++ e ∷ z)
              (𝕃.wordsBy P? x ++ 𝕃.wordsBy P? z))
      uit = {!!}
      open ≡-Reasoning

    konkf : (x z : String)
          → spit (x ++ "," ++ z) ≡ spit x ++ spit z
    konkf = λ x z → begin
      spit (x ++ "," ++ z) ≡⟨ {!!} ⟩
      spit x ++ spit z ∎
      where
      open ≡-Reasoning

    konk : (x z : String)
         → ',' ∉ x
         → spit (x ++ "," ++ z) ≡ 𝕊.toList x ∷ spit z
    konk = {!!}

  module Ps where
    du : readMaybe ∘ show ≗ just
       → {n : ℕ}
       → (x : Fin n)
       → just x ≡ ps (𝕊.toList $ show $ 𝔽.toℕ x)
    du rimco x = sym $ begin
      ps (𝕊.toList $ show x) ≡⟨ refl ⟩
      b𝔽 (rM $ id' $ show x) ≡⟨ id'∘show≡show x ▹ cong (b𝔽 ∘ rM) ⟩
      b𝔽 (rM $ show x) ≡⟨ rimco (𝔽.toℕ x) ▹ cong b𝔽 ⟩
      b𝔽 (just $ 𝔽.toℕ x) ≡⟨ refl ⟩
      just (𝔽.toℕ x) >>= fromℕ? ≡⟨ refl ⟩
      fromℕ? (𝔽.toℕ x) ≡⟨ refl ⟩
      mapₘ 𝔽.fromℕ< (decToMaybe $ 𝔽.toℕ x ℕ.<? _) ≡⟨ refl ⟩
      _ ≡⟨ zmadekydu'i ▹ cong (mapₘ 𝔽.fromℕ<) ⟩
      mapₘ 𝔽.fromℕ< (just $ DFP.toℕ<n x) ≡⟨ refl ⟩
      just _ ≡⟨ DFP.fromℕ<-toℕ _ _ ▹ cong just ⟩
      just x ∎
      where
      rM = readMaybe
      b𝔽 = _>>= fromℕ?
      id' = 𝕊.fromList ∘ 𝕊.toList
      id'∘show≡show : {n : ℕ} → (x : Fin n) → id' (show x) ≡ show x
      id'∘show≡show = fromList∘toList ∘ show
      open ≡-Reasoning

    nada : (j : String)
         → ¬_ $ Σ (∃ Fin) $ _≡_ j ∘ show ∘ proj₂
         → {n : ℕ}
         → nothing ≡ ps {n = n} (𝕊.toList j)
    nada j J {n} = sym $ begin
      ps {n = n} (tL j) ≡⟨ refl ⟩
      (fromℕ? <=< (readMaybe ∘ fL)) (tL j) ≡⟨ refl ⟩
      f? (readMaybe $ fL $ tL j) ≡⟨ [fL[tLj]≡j]' ⟩
      f? (readMaybe j) ≡⟨ rimnos j J ▹ cong f? ⟩
      f? nothing ≡⟨ refl ⟩
      nothing ∎
      where
      tL = 𝕊.toList
      fL = 𝕊.fromList
      f? : Maybe ℕ → Maybe $ Fin n
      f? = fromℕ? =<<_
      [fL[tLj]≡j]' = fromList∘toList j ▹_ $ cong $ f? ∘ readMaybe
      open ≡-Reasoning
      rimnos : (s : String)
             → ¬_ $ Σ (∃ Fin) $ _≡_ s ∘ show ∘ proj₂
             → readMaybe s ≡ nothing {A = ℕ}
      rimnos = {!!}

  module Pork where
    du : {n : ℕ}
       → {x z : Fin n}
       → (djb : x 𝔽.≤ z)
       → (_≡_
           (pork $ just x ∷ just z ∷ [])
           (just $ (_ , z) , djb))
    du {_} {x} {z} djb = begin
      pork (just x ∷ just z ∷ []) ≡⟨ refl ⟩
      mapₘ ((x , z) ,_) (decToMaybe $ x 𝔽.≤? z) ≡⟨ refl ⟩
      _ ≡⟨ zmadekydu'i {m = djb} ▹ cong (mapₘ (Σ.-,_)) ⟩
      mapₘ ((x , z) ,_) (just djb) ≡⟨ refl ⟩
      just ((x , z) , djb) ∎
      where
      open ≡-Reasoning

    nada : {n : ℕ}
         → {x z : Fin n}
         → ¬_ $ x 𝔽.≤ z
         → pork (just x ∷ just z ∷ []) ≡ nothing
    nada {x = x} {z} j = begin
      pork (just x ∷ just z ∷ []) ≡⟨ refl ⟩
      mapₘ Σ.-,_ (decToMaybe $ x 𝔽.≤? z) ≡⟨ refl ⟩
      _ ≡⟨ DN ▹ cong (mapₘ Σ.-,_) ⟩
      nothing ∎
      where
      DN = dec-nothing (𝔽._≤ _) (_ 𝔽.≤? _) j
      open ≡-Reasoning

  pav : ((x : ℕ) → readMaybe (show x) ≡ just x)
      → {n : ℕ}
      → (a b : Fin n)
      → (djb : a 𝔽.≤ b)
      → (_≡_
          (orsygenturfa'i $ show a ++ "," ++ show b)
          (just $ (a , b) , djb))
  pav rimco a b djb = begin
    orsygenturfa'i (show a ++ "," ++ show b) ≡⟨ refl ⟩
    pork (𝕃.map ps $ spit a,b) ≡⟨ cong pork mapyjus ⟩
    pork (just a ∷ just b ∷ []) ≡⟨ Pork.du djb ⟩
    just ((a , b) , djb) ∎
    where
    a,b = show a ++ "," ++ show b

    open ≡-Reasoning
    mapyjus = begin
      𝕃.map ps (spit a,b) ≡⟨ spidus a b ▹ cong (𝕃.map ps) ⟩
      𝕃.map ps (showF' a ∷ showF' b ∷ []) ≡⟨ refl ⟩
      𝕃.map justF' (a ∷ b ∷ []) ≡⟨ justymapdu $ a ∷ b ∷ [] ⟩
      𝕃.map just (a ∷ b ∷ []) ≡⟨ refl ⟩
      just a ∷  just b ∷ [] ∎
      where
      showF' : {n : ℕ} → Fin n → List Char
      showF' = 𝕊.toList ∘ show
      justF' : {n : ℕ} → Fin n → Maybe $ Fin n
      justF' = ps ∘ showF'
      justF'≡just : {n : ℕ} → (x : Fin n) → justF' x ≡ just x
      justF'≡just = sym ∘ Ps.du rimco
      justymapdu : {n : ℕ}
                 → (L : List $ Fin n)
                 → 𝕃.map justF' L ≡ 𝕃.map just L
      justymapdu = DLP.map-cong justF'≡just
      spidus : {n : ℕ}
             → (a b : Fin n)
             → (_≡_
                 (spit $ show a ++ "," ++ show b)
                 (showF' a ∷ showF' b ∷ []))
      spidus a b = Spit.du (s a) (s b) (nokom a) (nokom b) {!!} {!!}
        where
        s = show
        nokom : {n : ℕ} → (x : Fin n) → ',' ∉ 𝕊.toList (show x)
        nokom = {!!}
\end{code}

\section{la'oi .\F{orsygenturfa'i₃}.}
ni'o ro da xi pa poi ke'a ctaipe ko'a goi la'o zoi.\ \D{Fin} \B n\ .zoi.\ zo'u ro da xi re poi ke'a ctaipe ko'a zo'u do da xi ci poi ke'a ctaipe ko'a zo'u ro de poi ctaipe lo su'u ke'a cmima lo'i ro lerfu po le glibau ge'u poi ke'a me'oi .minuscule.\ zo'u ga jonai ko'e goi la'o zoi.\ \F{orsygenturfa'i₃} \B x\ .zoi.\ du la'oi .\IC{nothing}.\ gi ga je la'oi .\B x.\ konkatena lo sinxa be da xi pa lo me'oi .comma.\ lo sinxa be da xi re de lo sinxa be da xi ci gi ko'e me'oi .\IC{just}.\ lo .orsi be li re bei lo .orsi be li re bei lo .orsi be li re bei da xi pa bei da xi re be'o bei zo'e be'o bei da xi ci

\begin{code}
module Orsygenturfa'i₃ where
  lispork : List $ List String → Maybe $ (String × String) × String
  lispork ((a ∷ []) ∷ (b ∷ c ∷ []) ∷ []) = just $ (a , b) , c
  lispork _ = nothing

  orsispita : String → Maybe $ (String × String) × String
  orsispita = lispork ∘ 𝕃.map (w aintDigit?) ∘ w (_≟ ',')
    where
    w = 𝕊.wordsBy
    aintDigit? = T? ∘ 𝔹.not ∘ isDigit

  pork : {n : ℕ}
       → (String × String) × String
       → Maybe $ Σ (Fin n × Fin n) (uncurry 𝔽._≤_) × Maybe (Fin n)
  pork ((a , b) , c) = ax ,ₘ readMaybe' c
    where
    ax = R >>= λ (a' , b') → Orsygenturfa'i.pork $ just a' ∷ just b' ∷ []
      where
      R = readMaybe a ,ₘ readMaybe b

  orsygenturfa'i₃ : {n : ℕ}
                  → String
                  → (Maybe $ _×_
                      (∃ $ uncurry $ 𝔽._≤_ {n})
                      (Maybe $ Fin n))
  orsygenturfa'i₃ = pork <=< orsispita

open Orsygenturfa'i₃
  using (
    orsygenturfa'i₃
  )
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{orsygenturfa'i₃}.\ mapti}

\begin{code}
module Orsygenturfa'i₃Veritas where
  open Orsygenturfa'i₃

  lisporv : (a b c : String)
          → (_≡_
              (lispork $ (a ∷ []) ∷ (b ∷ c ∷ []) ∷ [])
              (just $ (a , b) , c))
  lisporv _ _ _ = refl

  lisporn : (x : List $ List String)
          → (¬_ $ Σ
              (String × String × String)
              (λ (a , b , c) → (x ≡ (a ∷ []) ∷ (b ∷ c ∷ []) ∷ [])))
          → lispork x ≡ nothing
  lisporn ((a ∷ []) ∷ (b ∷ c ∷ []) ∷ []) = _⇒⇐_ (_ , refl)
  lisporn [] N = {!!}
  lisporn x N = {!!}

  lisporn' : (x : List $ List String)
           → lispork x ≡ nothing
           → (¬_ $ Σ
               (String × String × String)
               (λ (a , b , c) → (x ≡ (a ∷ []) ∷ (b ∷ c ∷ []) ∷ [])))
  lisporn' = {!!}

  orspiv : (a b c : ℕ)
         → (x : Char)
         → false ≡ isDigit x
         → let x' = 𝕊.fromChar x in
           (_≡_
             (just $ (show a , show b) , show c)
             (orsispita
               (show a ++ "," ++ show b ++ x' ++ show c)))
  orspiv a b c x j = sym $ begin
    orsispita K ≡⟨ refl ⟩
    L (𝕃.map (w aD?) $ w (_≟ ',') K) ≡⟨ {!!} ⟩
    L' (𝕃.map (w' aD?) $ w' (_≟ ',') K') ≡⟨ {!!} ⟩
    L' (𝕃.map (w' aD?) $ s' a ∷ [ s'bxs'c ]) ≡⟨ refl ⟩
    L' (w' aD? (s' a) ∷ 𝕃.map (w' aD?) [ s'bxs'c ]) ≡⟨ refl ⟩
    _ ≡⟨ uadysas a ▹ cong (L' ∘ (_∷ 𝕃.map (w' aD?) [ s'bxs'c ])) ⟩
    L' ([ s' a ] ∷ 𝕃.map (w' aD?) [ s'bxs'c ]) ≡⟨ refl ⟩
    L' ([ s' a ] ∷ [ w' aD? s'bxs'c ])  ≡⟨ refl ⟩
    _ ≡⟨ sabus ▹ cong (L' ∘ _∷_ ([ s' a ]) ∘ [_]) ⟩
    L' ([ s' a ] ∷ [ s' b ∷ [ s' c ] ]) ≡⟨ refl ⟩
    L' (map₂ s' abj) ≡⟨ refl ⟩
    L (map₂ (𝕊.fromList ∘ s') abj) ≡⟨ map₂-cong fL∘tL _ ▹ cong L ⟩
    L (map₂ s abj) ≡⟨ refl ⟩
    L ([ s a ] ∷ [ s b ∷ [ s c ] ]) ≡⟨ refl ⟩
    just ((show a , show b) , show c) ∎
    where
    L = lispork
    [_] = 𝕃.[_]
    w = 𝕊.wordsBy
    w' = 𝕃.wordsBy
    aD? = T? ∘ 𝔹.not ∘ isDigit
    K = show a ++ "," ++ show b ++ 𝕊.fromChar x ++ show c
    s = show
    s' = 𝕊.toList ∘ show
    s'bxs'c = s' b ++ x ∷ s' c
    fL∘tL : (x : String) → 𝕊.fromList (𝕊.toList x) ≡ x
    fL∘tL = fromList∘toList
    K' = s' a ++ ',' ∷ s' b ++ x ∷ s' c
    abj = [ a ] ∷ [ b ∷ [ c ] ]
    sabus : w' aD? s'bxs'c ≡ s' b ∷ [ s' c ]
    sabus = {!!}
    uadysas : (a : ℕ) → w' aD? (s' a) ≡ [ s' a ]
    uadysas = {!!}
    map₂ : ∀ {a b} → {A : Set a} → {B : Set b}
         → (A → B) → List $ List A → List $ List B
    map₂ = 𝕃.map ∘ 𝕃.map
    L' : List $ List $ List $ Char
       → Maybe $ (String × String) × String
    L' = L ∘_ $ 𝕃.map $ 𝕃.map 𝕊.fromList
    map₂-cong = DLP.map-cong ∘ DLP.map-cong
    open ≡-Reasoning

  porkcos : {n : ℕ}
          → (a b : Fin n)
          → (d : a 𝔽.≤ b)
          → (c : Fin n)
          → (_≡_
              (pork $ (show a , show b) , show c)
              (just $ ((a , b) , d) , just c))
  porkcos a b d c = begin
    pork ((show a , show b) , show c) ≡⟨ refl ⟩
    _,ₘ_ ax (readMaybe' $ show c) ≡⟨ rimcos c ▹ cong (_,ₘ_ ax) ⟩
    _,ₘ_ ax (just $ just c) ≡⟨ ax≡justabd ▹ cong (_,ₘ just (just c)) ⟩
    _,ₘ_ (just $ (a , b) , d) (just $ just c) ≡⟨ refl ⟩
    just (((a , b) , d) , just c) ∎
    where
    R = readMaybe (show a) ,ₘ readMaybe (show b)
    ax : Maybe $ Σ (Fin _ × Fin _) $ uncurry 𝔽._≤_
    ax = R >>= λ (a' , b') → Orsygenturfa'i.pork $ just a' ∷ just b' ∷ []
    rimcos : {n : ℕ}
           → readMaybe' ∘ show ≗ just ∘ just {A = Fin n}
    rimcos = ReadMaybe'Veritas.namcu
    open ≡-Reasoning
    ax≡justabd : ax ≡ just ((a , b) , d)
    ax≡justabd = begin
      ax ≡⟨ refl ⟩
      (R >>= jminaCtaipe) ≡⟨ R≡justab ▹ cong (_>>= jminaCtaipe) ⟩
      (just (a , b) >>= jminaCtaipe) ≡⟨ refl ⟩
      jminaCtaipe (a , b) ≡⟨ refl ⟩
      Orsygenturfa'i.pork (just a ∷ just b ∷ []) ≡⟨ refl ⟩
      _ ≡⟨ Orsygenturfa'iVeritas.Pork.du d ⟩
      just ((a , b) , d) ∎
      where
      jminaCtaipe : {n : ℕ}
                  → Fin n × Fin n
                  → Maybe $ Σ (Fin n × _) $ uncurry 𝔽._≤_
      jminaCtaipe (a , b) = Orsygenturfa'i.pork $ just a ∷ just b ∷ []
      R≡justab : R ≡ just (a , b)
      R≡justab = begin
        R ≡⟨ refl ⟩
        readMaybe (show a) ,ₘ readMaybe (show b) ≡⟨ refl ⟩
        _ ≡⟨ readMaybe∘show a ▹ cong (_,ₘ readMaybe (show b)) ⟩
        just a ,ₘ readMaybe (show b) ≡⟨ refl ⟩
        _ ≡⟨ readMaybe∘show b ▹ cong (just a ,ₘ_) ⟩
        just a ,ₘ just b ≡⟨ refl ⟩
        just (a , b) ∎

  pav : {n : ℕ}
      → (v x z : Fin n)
      → (d : v 𝔽.≤ x)
      → (c : Char)
      → false ≡ isDigit c
      → (_≡_
          (just $ ((v , x) , d) , just z)
          (orsygenturfa'i₃
            (show v ++ "," ++ show x ++ 𝕊.fromChar c ++ show z)))
  pav v x z d c j = sym $ begin
    orsygenturfa'i₃ (k₃ v x c z) ≡⟨ refl ⟩
    orsispita (k₃ v x c z) >>= pork ≡⟨ refl ⟩
    orsispita (k₃ (t v) (t x) c $ t z) >>= pork ≡⟨ refl ⟩
    _ ≡⟨ orspiv (t v) (t x) (t z) c j ▹ sym ▹ cong (_>>= pork) ⟩
    just ((show (t v) , show (t x)) , show (t z)) >>= pork ≡⟨ refl ⟩
    pork ((show (t v) , show (t x)) , show (t z)) ≡⟨ refl ⟩
    pork ((show v , show x) , show z) ≡⟨ porkcos v x d z ⟩
    just (((v , x) , d) , just z) ∎
    where
    t = 𝔽.toℕ
    k₃ : ∀ {a b c} → {A : Set a} → {B : Set b} → {C : Set c}
       → ⦃ Show A ⦄ → ⦃ Show B ⦄ → ⦃ Show C ⦄
       → A → B → Char → C → String
    k₃ v x c z = show v ++ "," ++ show x ++ c' ++ show z
      where
      c' = 𝕊.fromChar c
    open ≡-Reasoning
\end{code}

\chapter{zo'e je le fancu pe la'oi .\D{Cmd}.}

\section{la'oi .\F{reed}.}
ni'o ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{reed} \B x \B s\ .zoi.\ gi ga je la'oi .\B s.\ midnoi fo la'o zoi.\ \Xr{ed}{1} .zoi.\ je cu mapti la'o zoi.\ \D{Cmd} \B x\ .zoi.\ gi ko'a me'oi .\IC{just}.\ lo mapti be la'oi .\B s.

\begin{code}
module Reed where
  module No where
    g : {x : Buffer} → Char → Maybe $ Cmd x
    g {x} 'w' = mapₘ Rejgau $ Buffer.datnyveicme x
    g 'u' = mapₘ Xruti $ 𝕃.head $ 𝕃.allFin _
    g 'q' = just Sisti
    g 'Q' = just Sisti!
    g _ = nothing

    k : {x : Buffer} → List String → Maybe $ Cmd x
    k ("w" ∷ xs@(_ ∷ _)) = just $ Rejgau $ 𝕊.unwords xs
    k _ = nothing

    t : {x : Buffer} → String → Maybe $ Cmd x
    t = g <=< (𝕃.head ∘ 𝕊.toList)

  module Pa where
    g : {x : Buffer} → Buffer.F x → Char → Maybe $ Cmd x
    g n 'a' = just $ Jmina n
    g n 'i' = just $ Jmini n
    g _ _ = nothing

    t : {x : Buffer} → String → Maybe $ Cmd x
    t {x} s = uncurry g =<<_ $ _,ₘ_ n $ 𝕃.last $ 𝕊.toList s
      where
      n = pamoinamcu s >>= fromℕ?

  module Re where
    g : (x : Buffer)
      → (a b : Buffer.F x)
      → (a 𝔽.≤ b)
      → Char
      → Maybe $ Cmd x
    g x a b z j with j
    ... | 'c' = just $ Basti a b z
    ... | 'd' = just $ Vimcu a b z
    ... | 'n' = just $ Namcusku a b z
    ... | 'p' = just $ Cusku a b z
    ... | _ = nothing

    t : {x : Buffer} → String → Maybe $ Cmd x
    t {x} s = _>>= g' $ (Data.Maybe.ap ∘₂ mapₘ) _,_ (romoi s) og
      where
      og = orsygenturfa'i $ romoivimcu s
      romoi = 𝕃.last ∘ 𝕊.toList
      g' = λ (r , _ , z) → g x _ _ z r

  module Ci where
    g : {x : Buffer}
      → (a b : Buffer.F x)
      → Maybe $ Buffer.F x
      → a 𝔽.≤ b
      → Char
      → Maybe $ Cmd x
    g a b c d x with x
    ... | 'm' = just $ Muvgau a b c d
    ... | _ = nothing

    t : {x : Buffer} → String → Maybe $ Cmd x
    t {x} s = g' =<<_ $ c ,ₘ orsygenturfa'i₃ s
      where
      g' = λ (z , (_ , d) , c) → g _ _ c d z
      c = f $ 𝕃.filter aintDigit? $ 𝕊.toList s
        where
        aintDigit? = T? ∘ 𝔹.not ∘ isDigit
        f = λ {(x ∷ []) → just x; _ → nothing}

  terp : {x : Buffer} → String → List $ Maybe $ Cmd x
  terp s = No.t s ∷ Pa.t s ∷ Re.t s ∷ No.k s' ∷ []
    where
    s' = 𝕊.wordsBy (_≟ ' ') s

  reed : (x : Buffer) → String → Maybe $ Cmd x
  reed x = 𝕃.head ∘ 𝕃.mapMaybe id ∘ terp

open Reed
  using (
    reed
  )
\end{code}

\subsection{le krinu be le me'oi .\AgdaKeyword{module}.\ co'e}
ni'o pilno ko'a goi le me'oi .\AgdaKeyword{module}.\ co'e ki'u le su'u tu'a ko'a filri'a lo nu ciksi lo ctaipe be le su'u mapti  .i la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi lo steci be la'oi .\F{reed}.\ jenai zo'e bau la .lojban.

\subsection{le cmene be le me'oi .\AgdaKeyword{module}.\ fancu}
ni'o zo .k.\ cmavlaka'i zo konkatena

.i zo .t.\ cmavlaka'i zo tolsti

.i cumki fa lo nu su'o da zo'u zo .g.\ cmavlaka'i da

\subsection{le ctaipe be le su'u la'oi .\F{reed}.\ mapti}

\begin{code}
module ReedVeritas where
  open ≡-Reasoning

  private
    k₁ : (x : Buffer)
       → (a : Buffer.F x)
       → Char
       → String
    k₁ _ a x = show (𝔽.toℕ a) ++ 𝕊.fromChar x

    k₂ : (x : Buffer)
       → (a b : Buffer.F x)
       → Char
       → String
    k₂ _ a b x = f a ++ "," ++ f b ++ 𝕊.fromChar x
      where
      f = show ∘ 𝔽.toℕ

    k₃ : (x : Buffer)
       → (a b c : Buffer.F x)
       → Char
       → String
    k₃ x a b c s = k₂ x a b s ++ show (𝔽.toℕ c)

  module No where
    uin : (x : Buffer)
        → reed x "w" ≡ mapₘ Rejgau (Buffer.datnyveicme x)
    uin x = begin
      reed x "w" ≡⟨ refl ⟩
      𝕃.head (𝕃.mapMaybe id L) ≡⟨ duridos ⟩
      𝕃.head (𝕊.toList "w") >>= Reed.No.g ≡⟨ refl ⟩
      mapₘ Rejgau (Buffer.datnyveicme x) ∎
      where
      open Reed
      ridos = 𝕃.head (𝕊.toList "w") >>= Reed.No.g
      L = ridos ∷ _
      duridos : 𝕃.head (𝕃.mapMaybe id L) ≡ ridos
      duridos with ridos
      ... | just _ = refl
      ... | nothing = refl

    -- ni'o la .varik. cu stidi lo nu tcidu le velcki be
    -- la .uin. fa lo na jimpe be fi la .kybin. je la'oi
    -- .kybin'.

    kybin : (x : Buffer)
          → reed x "q" ≡ just Sisti
    kybin _ = refl

    kybin' : (x : Buffer)
           → reed x "Q" ≡ just Sisti!
    kybin' _ = refl

    xon : (x : Buffer)
        → (z : ∃ λ n → suc n ≡ length (Buffer.citri x))
        → reed x "u" ≡ just (Xruti $ mink 𝔽.zero $ proj₂ z)
    xon x z = begin
      reed x "u" ≡⟨ refl ⟩
      𝕃.head (𝕃.mapMaybe id $ Reed.terp "u") ≡⟨ refl ⟩
      𝕃.head (𝕃.mapMaybe id terp') ≡⟨ xedrenod 3 $ Reed.No.t "u" ⟩
      𝕃.head (𝕃.mapMaybe id $ Reed.No.t "u" ∷ []) ≡⟨ noxed _ ▹ sym ⟩
      Reed.No.t "u" ≡⟨ refl ⟩
      mapₘ X (𝕃.head $ 𝕃.allFin _) ≡⟨ dzeroxe z ▹ cong (mapₘ X) ⟩
      just (X $ mink 𝔽.zero $ proj₂ z) ∎
      where
      X = Xruti
      terp' = Reed.No.t "u" ∷ 𝕃.replicate 3 nothing
      dzeroxe : {n : ℕ}
              → (z : ∃ $ (_≡ n) ∘ suc)
              → 𝕃.head (𝕃.allFin n) ≡ just (mink 𝔽.zero $ proj₂ z)
      dzeroxe (_ , refl) = refl
      noxed : ∀ {a} → {A : Set a}
            → (x : Maybe A)
            → x ≡_ $ 𝕃.head $ 𝕃.mapMaybe id $ x ∷ []
      noxed nothing = refl
      noxed (just _) = refl
      xedrenod : ∀ {a} → {A : Set a}
               → (n : ℕ)
               → (x : Maybe A)
               → ((_≡_ on_ $ 𝕃.head ∘ 𝕃.mapMaybe id ∘ _∷_ x)
                   (𝕃.replicate n nothing)
                   [])
      xedrenod _ (just _) = refl
      xedrenod 0 nothing = refl
      xedrenod (suc n) nothing = xedrenod n nothing

  ac : (x : Buffer)
     → (a : Buffer.F x)
     → just (Jmina a) ≡ reed x (k₁ x a 'a')
  ac x a = sym $ begin
    reed x (k₁ x a 'a') ≡⟨ refl ⟩
    reed x K ≡⟨ {!!} ⟩
    Reed.Pa.t K ≡⟨ refl ⟩
    _,ₘ_ (pamoinamcu K >>= fromℕ?) (sl K) >>= g' ≡⟨ refl ⟩
    _ ≡⟨ rms≡[pK>>=fℕ?] ▹ sym ▹ cong (λ x → _,ₘ_ x (sl K) >>= g') ⟩
    _,ₘ_ (rms a) (sl K) >>= g' ≡⟨ refl ⟩
    _ ≡⟨ silkas ▹ cong (λ c → _,ₘ_ (rms a) c >>= g') ⟩
    _,ₘ_ (rms a) (just 'a') >>= g' ≡⟨ refl ⟩
    _ ≡⟨ readMaybe∘show a ▹ cong (λ x → _,ₘ_ x _ >>= g') ⟩
    _,ₘ_ (just a) (just 'a') >>= g' ≡⟨ refl ⟩
    just (a , 'a') >>= g' ≡⟨ refl ⟩
    Reed.Pa.g a 'a' ≡⟨ refl ⟩
    just (Jmina a) ∎
    where
    g' = uncurry Reed.Pa.g
    K = k₁ x a 'a'
    rms : {n : ℕ} → Fin n → Maybe $ Fin n
    rms = readMaybe ∘ show
    sl = 𝕃.last ∘ 𝕊.toList
    silkas : sl K ≡ just 'a'
    silkas = begin
      sl K ≡⟨ {!!} ⟩
      𝕃.last (𝕊.toList K) ≡⟨ {!!} ⟩
      𝕃.last (𝕊.toList $ k₁ x a 'a') ≡⟨ {!!} ⟩
      𝕃.last (𝕊.toList $ show (𝔽.toℕ a) ++ 𝕊.fromChar 'a') ≡⟨ {!!} ⟩
      just 'a' ∎
    rms≡[pK>>=fℕ?] : rms a ≡ pamoinamcu K >>= fromℕ?
    rms≡[pK>>=fℕ?] = sym $ begin
      pamoinamcu K >>= fromℕ? ≡⟨ D ∋ {!!} ▹ cong (_>>= fromℕ?) ⟩
      just (𝔽.toℕ a) >>= fromℕ? ≡⟨ refl ⟩
      fromℕ? (𝔽.toℕ a) ≡⟨ {!!} ⟩
      just a ≡⟨ {!!} ⟩
      rms a ∎
      where
      D = pamoinamcu K ≡ just (𝔽.toℕ a)

  ic : (x : Buffer)
     → (a : Buffer.F x)
     → just (Jmini a) ≡ reed x (k₁ x a 'i')
  ic x a = sym $ begin
    reed x (k₁ x a 'i') ≡⟨ refl ⟩
    reed x K ≡⟨ {!!} ⟩
    Reed.Pa.t K ≡⟨ {!!} ⟩
    _,ₘ_ (pamoinamcu K >>= fromℕ?) (sl "i") >>= g' ≡⟨ (pamoinamcu K >>= fromℕ? ≡ rms a) ∋ {!!} ▹ cong (λ x → _,ₘ_ x (sl "i") >>= g') ⟩
    _,ₘ_ (rms a) (sl "i") >>= g' ≡⟨ refl ⟩
    _,ₘ_ (rms a) (just 'i') >>= g' ≡⟨ refl ⟩
    _ ≡⟨ rimco a ▹ cong (λ x → _,ₘ_ x _ >>= g') ⟩
    _,ₘ_ (just a) (just 'i') >>= g' ≡⟨ refl ⟩
    just (a , 'i') >>= g' ≡⟨ refl ⟩
    Reed.Pa.g a 'i' ≡⟨ refl ⟩
    just (Jmini a) ∎
    where
    g' = uncurry Reed.Pa.g
    K = k₁ x a 'i'
    rms : {n : ℕ} → Fin n → Maybe $ Fin n
    rms = readMaybe ∘ show
    sl = 𝕃.last ∘ 𝕊.toList
    rimco : {n : ℕ} → (x : Fin n) → rms x ≡ just x
    rimco = readMaybe∘show

  mixer : (x : Buffer)
        → (a b c : Buffer.F x)
        → (d : a 𝔽.≤ b)
        → just (Muvgau a b (just c) d) ≡ reed x (k₂ x a b 'm')
  mixer x a b c d = {!!}

  vim : (x : Buffer)
      → (a b : Buffer.F x)
      → (d : a 𝔽.≤ b)
      → just (Vimcu a b d) ≡ reed x (k₂ x a b 'd')
  vim x a b d = sym $ begin
    reed x (k₂ x a b 'd') ≡⟨ {!!} ⟩
    Reed.Re.t (k₂ x a b 'd') ≡⟨ refl ⟩
    _,ₘ_ (romoi K₂) (o∘r K₂) >>= g' ≡⟨ refl ⟩
    _ ≡⟨ romoiK₂≡justd ▹ cong (λ e → (e ,ₘ o∘r K₂) >>= g') ⟩
    _,ₘ_ (just 'd') (o∘r K₂) >>= g' ≡⟨ {!!} ⟩
    _,ₘ_ (just 'd') (just $ (a , b) , d) >>= g' ≡⟨ refl ⟩
    Reed.Re.g x a b d 'd' ≡⟨ refl ⟩
    just (Vimcu a b d) ∎
    where
    K₂ = k₂ x a b 'd'
    BL = Buffer.lerpinste x
    romoi = 𝕃.last ∘ 𝕊.toList
    g' = λ (r' , _ , z) → Reed.Re.g x _ _ z r'
    o∘r = orsygenturfa'i {n = length BL} ∘ romoivimcu
    romoiK₂≡justd : romoi K₂ ≡ just 'd'
    romoiK₂≡justd = {!!}

  uip : ((s : String) → s ≡_ $ 𝕊.unwords $ 𝕊.wordsBy (_≟ ' ') s)
      → (x : Buffer)
      → (s : String)
      → (c : Char)
      → ¬_ $ c ≡ ' '
      → let c∷s = 𝕊.fromChar c ++ s in
        Data.Maybe.Is-just $ 𝕃.uncons $ 𝕊.wordsBy (_≟ ' ') c∷s
      → just (Rejgau c∷s) ≡ reed x ("w " ++ c∷s)
  uip unwords∘w x s c n uj = sym $ begin
    reed x ("w " ++ c∷s) ≡⟨ w++s≡w++ws ▹ cong (reed x) ⟩
    reed x (unwords $ "w" ∷ w c∷s) ≡⟨ refl ⟩
    rx (unwords $ "w" ∷ w c∷s) ≡⟨ reedx≡k∘w $ unwords $ "w" ∷ w c∷s ⟩
    k (w $ unwords $ "w" ∷ w c∷s) ≡⟨ w∘unwords _ ▹ sym ▹ cong k ⟩
    k ("w" ∷ w c∷s) ≡⟨ w[c∷s]≡v₁∷v₂ ▹ cong (k ∘ _∷_ "w") ⟩
    k ("w" ∷ v₁ ∷ v₂) ≡⟨ refl ⟩
    j∘R (unwords $ v₁ ∷ v₂) ≡⟨ refl ⟩
    j∘R _ ≡⟨ w[c∷s]≡v₁∷v₂ ▹ sym ▹ cong (j∘R ∘ unwords) ⟩
    j∘R (unwords $ w c∷s) ≡⟨ unwords∘w c∷s ▹ sym ▹ cong j∘R ⟩
    j∘R c∷s ∎
    where
    open Reed.No using (k)
    rx = reed x
    c∷s = 𝕊.fromChar c ++ s
    w = 𝕊.wordsBy $ _≟ ' '
    v = Data.Maybe.to-witness uj
    v₁ = proj₁ v
    v₂ = proj₂ v
    j∘R = just ∘ Rejgau
    w[c∷s]≡v₁∷v₂ : w c∷s ≡ v₁ ∷ v₂
    w[c∷s]≡v₁∷v₂ = consunwords uj
      where
      consunwords : ∀ {a} → {A : Set a}
                  → {xs : List A}
                  → (j : Is-just $ 𝕃.uncons xs)
                  → let j' = Data.Maybe.to-witness j in
                    xs ≡ proj₁ j' ∷ proj₂ j'
      consunwords {xs = _ ∷ _} (DMA.just j) = refl
    unwords = 𝕊.unwords
    open Reed
    reedx≡k∘w : (s : String) → reed x s ≡ k (w s)
    reedx≡k∘w = {!!}
    w∘unwords : (x : List String) → x ≡ w (unwords x)
    w∘unwords = {!!}
    w++s≡w++ws : "w " ++ c∷s ≡ unwords ("w" ∷ w c∷s)
    w++s≡w++ws = sym $ begin
      unwords ("w" ∷ w c∷s) ≡⟨ unwords-dist "w" (w c∷s) $ ++-¬[] c s ⟩
      "w " ++ unwords (w c∷s) ≡⟨ refl ⟩
      _ ≡⟨ unwords∘w c∷s ▹ sym ▹ cong ("w " ++_) ⟩
      "w " ++ c∷s ∎
      where
      ++-¬[] : (c : Char)
             → (s : String)
             → ¬_ $ w (𝕊.fromChar c ++ s) ≡ []
      ++-¬[] = ∷→¬[] _ ∘₂ w-++-∷
        where
        ∷→¬[] : ∀ {a} → {A : Set a}
              → (x : List A)
              → ∃ $ _≡_ x ∘ uncurry _∷_
              → ¬_ $ x ≡ []
        ∷→¬[] _ (_ , refl) ()
        w-++-∷ : (c : Char)
               → (s : String)
               → (Σ
                   (String × List String)
                   ((w (𝕊.fromChar c ++ s) ≡_) ∘ uncurry _∷_))
        w-++-∷ c s = ∷-w (𝕊.fromChar c ++ _) {!!}
          where
          ∷-w : (s : String)
              → ¬_ $ s ≡ ""
              → ∃ $ (w s ≡_) ∘ uncurry _∷_
          ∷-w s n with 𝕊.toList s ≟ []
          ... | yes d = tL≡[]→x≡s[] d ⇒⇐ n
            where
            tL≡[]→x≡s[] : (_≡ []) ∘ 𝕊.toList ⊆ (_≡ "")
            tL≡[]→x≡s[] {""} refl = refl
            tL≡[]→x≡s[] {x} d = {!!}
          ... | no j = {!!}
      unwords-dist : (x : String)
                   → (z : List String)
                   → ¬_ $ z ≡ []
                   → (_≡_
                       (unwords $ x ∷ z)
                       ((x ++ " ") ++ unwords z))
      unwords-dist = {!!}
\end{code}

\section{la \F{kanji}}
ni'o la'o zoi.\ \F{kanji} \Sym\{\B x\Sym\} \B s\ .zoi.\ .orsi li re lo jalge be lo nu co'e la'oi .\B s.\ la'oi .\B x.\ kei zo'e poi ga jonai ke'a du la'oi .\IC{nothing}.\ gi ga jonai cadga fa lo nu cusku ke'a fo lo co'e co mu'oi glibau.\ standard output .glibau.\ gi\ldots ga je co'e gi la .varik.\ na birti lo du'u zabna ciksi fo ma kau bau la .lojban.  .i ku'i gu zabna ciksi bau la .lojban.\ gi ciksi le ctaipe be le su'u mapti

\begin{code}
kanji : {x : Buffer}
      → Cmd x
      → ∃ $ Maybe ∘ _⊎_ String ∘ Cmdᵢₒ
kanji {x} Sisti = x ,_ $ just $ inj₂ Sistiᵢₒ
kanji {x} Sisti! = x ,_ $ just $ inj₂ Sisti!ᵢₒ
kanji {x} (Jmina a) = x ,_ $ just $ inj₂ $ Tciduᵢₒ "/dev/stdin" a'
  where
  a' : Maybe $ Buffer.F x
  a' = mapₘ 𝔽.fromℕ< $ decToMaybe $ ℕ.suc (𝔽.toℕ a) ℕ.<? _
kanji {x} (Cusku a b _) = x ,_ $ just $ inj₁ $ unlines $ i BL
  where
  BL = Buffer.lerpinste x
  i = (𝔽.toℕ a) ↓_ ∘ (suc $ 𝔽.toℕ b) ↑_
kanji {x} (Namcusku a b m) = x ,_ $ just $ inj₁ $ viiet kot
  where
  kot = from-inj₁ $ from-just $ proj₂ $ kanji {x} $ Cusku a b m
  viiet = unlines ∘ 𝕃.map stringCat' ∘ uin ∘ lines
    where
    stringCat' = λ (x , z) → show x ++ "\t" ++ z
    uin : List String → List $ ℕ × String
    uin = 𝕃.zip $ 𝔽.toℕ a ↓_ $ 𝕃.upTo $ 𝔽.toℕ b ℕ.+ 1
kanji {x} (Muvgau a b c _) = x' , nothing
  where
  x' = record x {
    citri = Buffer.cninycitri x;
    cablerpinsle = mink (Buffer.cablerpinsle x) {!!};
    lerpinste = 𝔽.toℕ a ↑ BL ++ x₂ ++ {!!}
    }
    where
    BL = Buffer.lerpinste x
    x₂ = 𝔽.toℕ a ↓_ $ suc (𝔽.toℕ b) ↑ BL
kanji {x} (Vimcu a b _) = x' , nothing
  where
  x' = record x {
    citri = Buffer.cninycitri x;
    cablerpinsle = {!!};
    lerpinste = 𝔽.toℕ a ↑ Lz ++ suc (𝔽.toℕ b) ↓ Lz}
    where
    Lz = Buffer.lerpinste x
kanji {x} (Jmini n) = x ,_ $ just $ inj₂ $ Tciduᵢₒ "/dev/stdin" (just n)
kanji {x} (Rejgau d) = x ,_ $ just $ inj₂ $ Rejgauᵢₒ xul d
  where
  xul = unlines $ Buffer.lerpinste x
kanji {x} (Basti a b d) = kanji {x'} $ Jmini a'
  where
  a' = 𝔽.fromℕ< {𝔽.toℕ a} {!!}
  x' = proj₁ $ kanji {x} $ Vimcu a b d
kanji {x} (Xruti n) = {!!} , {!!}
\end{code}

\subsection{le ctaipe be le su'u la \F{kanji}\ cu mapti}

\begin{code}
module KanjyVeritas where
  sistid : (x : Buffer)
         → kanji {x} Sisti ≡_ $ x , just (inj₂ Sistiᵢₒ)
  sistid x = refl

  sistik : (x : Buffer)
         → kanji {x} Sisti! ≡_ $ x , just (inj₂ Sisti!ᵢₒ)
  sistik x = refl

  private
    Dunli₁ : (_ : {x : Buffer}
                → (a b : Buffer.F x)
                → (d : a 𝔽.≤ b)
                → Cmd x)
           → Set
    Dunli₁ C = {x : Buffer}
             → {a b : Buffer.F x}
             → {d : a 𝔽.≤ b}
             → x ≡_ $ proj₁ $ kanji {x} $ C a b d

  dub : Dunli₁ Cusku × Dunli₁ Namcusku
  dub = refl , refl

  jminam : (x : Buffer)
         → (a : Buffer.F x)
         → (M : suc (𝔽.toℕ a) ℕ.< length (Buffer.lerpinste x))
         → (_≡_
             (kanji {x} $ Jmina a)
             (_,_
               x
               (just $ inj₂ $ Tciduᵢₒ
                 "/dev/stdin"
                 (just $ 𝔽.fromℕ< M))))
  jminam x a M = cong (x ,_) $ begin
    proj₂ (kanji {x} $ Jmina a) ≡⟨ refl ⟩
    just (inj₂ $ Tciduᵢₒ "/dev/stdin" a') ≡⟨ refl ⟩
    F a' ≡⟨ refl ⟩
    F (mapₘ 𝔽.fromℕ< $ decToMaybe $ _ ℕ.<? _) ≡⟨ refl ⟩
    _ ≡⟨ DY ▹ proj₂ ▹ cong (F ∘ mapₘ 𝔽.fromℕ< ∘ decToMaybe) ⟩
    F (mapₘ 𝔽.fromℕ< $ decToMaybe $ yes $ proj₁ DY) ≡⟨ refl ⟩
    F (mapₘ 𝔽.fromℕ< $ just $ proj₁ DY) ≡⟨ refl ⟩
    F (just $ 𝔽.fromℕ< $ proj₁ DY) ≡⟨ refl ⟩
    _ ≡⟨ {!!} ▹ cong (F ∘ just ∘ 𝔽.fromℕ<) ⟩
    F (just $ 𝔽.fromℕ< M) ∎
    where
    open ≡-Reasoning
    a' = mapₘ 𝔽.fromℕ< $ decToMaybe $ _ ℕ.<? _
    DY = dec-yes (_ ℕ.<? _) M
    F = just ∘ inj₂ ∘ Tciduᵢₒ "/dev/stdin"

  jminaz : (x : Buffer)
         → (a : Buffer.F x)
         → ¬_ $ ℕ.suc (𝔽.toℕ a) ℕ.< length (Buffer.lerpinste x)
         → (_≡_
             (kanji {x} $ Jmina a)
             (x ,_ $ just $ inj₂ $ Tciduᵢₒ "/dev/stdin" nothing))
  jminaz x a N = cong (x ,_) $ begin
    proj₂ (kanji {x} $ Jmina a) ≡⟨ refl ⟩
    F a' ≡⟨ refl ⟩
    F (mapₘ 𝔽.fromℕ< $ decToMaybe $ _ ℕ.<? _) ≡⟨ refl ⟩
    _ ≡⟨ DN ▹ proj₂ ▹ cong (F ∘ mapₘ 𝔽.fromℕ< ∘ decToMaybe) ⟩
    F (mapₘ 𝔽.fromℕ< $ decToMaybe $ no $ proj₁ DN) ≡⟨ refl ⟩
    F nothing ∎
    where
    open ≡-Reasoning
    F = just ∘ inj₂ ∘ Tciduᵢₒ "/dev/stdin"
    DN = Relation.Nullary.Decidable.dec-no (_ ℕ.<? _) N
    a' = mapₘ 𝔽.fromℕ< $ decToMaybe $ ℕ.suc (𝔽.toℕ a) ℕ.<? _

  jminic : (x : Buffer)
         → (a : Buffer.F x)
         → (_≡_
             (kanji {x} $ Jmini a)
             (x ,_ $ just $ inj₂ $ Tciduᵢₒ "/dev/stdin" $ just a))
  jminic _ _ = refl

  vimcablerpinsles : (x : Buffer)
                   → (a b : Buffer.F x)
                   → (d : a 𝔽.≤ b)
                   → let BC = 𝔽.toℕ ∘ Buffer.cablerpinsle in
                     (_≡_
                       (BC $ proj₁ $ kanji {x} $ Vimcu a b d)
                       {!!})
  vimcablerpinsles = {!!}

  nilzilcmiv : (x : Buffer)
             → (a b : Buffer.F x)
             → (d : a 𝔽.≤ b)
             → let BLT = length ∘ Buffer.lerpinste in
               (_≡_
                 (BLT $ proj₁ $ kanji {x} $ Vimcu a b d)
                 (BLT x ℕ.∸_ $ suc $ 𝔽.toℕ b ℕ.∸ 𝔽.toℕ a))
  nilzilcmiv x a b d = begin
    lb x₂ ≡⟨ refl ⟩
    length (𝔽.toℕ a ↑ Lz ++ suc (𝔽.toℕ b) ↓ Lz) ≡⟨ refl ⟩
    length (a' ↑ Lz ++ b'+1 ↓ Lz) ≡⟨ DLP.length-++ $ a' ↑ Lz ⟩
    length (a' ↑ Lz) ℕ.+ length (b'+1 ↓ Lz) ≡⟨ refl ⟩
    _ ≡⟨ DLP.length-drop b'+1 Lz ▹ cong (ℕ._+_ _) ⟩
    length (a' ↑ Lz) ℕ.+ (length Lz ℕ.∸ b'+1) ≡⟨ refl ⟩
    length (a' ↑ Lz) ℕ.+ (lb x ℕ.∸ b'+1) ≡⟨ refl ⟩
    _ ≡⟨ finlenteik Lz a ▹ cong (ℕ._+ (lb x ℕ.∸ b'+1)) ⟩
    a' ℕ.+ (lb x ℕ.∸ b'+1) ≡⟨ DNP.+-comm a' _ ⟩
    lb x ℕ.∸ b'+1 ℕ.+ a' ≡⟨ v∸x+z≡v∸[x∸z] $ flex d ⟩
    lb x ℕ.∸ (b'+1 ℕ.∸ a') ≡⟨ refl ⟩
    lb x ℕ.∸ (suc b' ℕ.∸ a') ≡⟨ suc-dist-∸ d ▹ cong (lb x ℕ.∸_) ⟩
    lb x ℕ.∸ suc (b' ℕ.∸ a') ≡⟨ refl ⟩
    lb x ℕ.∸ suc (𝔽.toℕ b ℕ.∸ 𝔽.toℕ a) ∎
    where
    b' = 𝔽.toℕ b
    b'+1 = suc b'
    a' = 𝔽.toℕ a
    Lz = Buffer.lerpinste x
    x₂ = proj₁ $ kanji {x} $ Vimcu a b d
    lb = length ∘ Buffer.lerpinste
    flex : {a : ℕ}
         → {m n : Fin a}
         → n 𝔽.≤ m
         → 𝔽.toℕ n ℕ.≤ suc (𝔽.toℕ m)
    flex = flip DNP.≤-trans $ DNP.n≤1+n _
    open ≡-Reasoning
    finlenteik : ∀ {a} → {A : Set a}
               → (x : List A)
               → (n : Fin $ length x)
               → length (𝔽.toℕ n ↑ x) ≡ 𝔽.toℕ n
    finlenteik (_ ∷ _) 𝔽.zero = refl
    finlenteik (_ ∷ xs) (𝔽.suc n) = finlenteik xs n ▹ cong suc
    v∸x+z≡v∸[x∸z] : {v x z : ℕ}
                 → z ℕ.≤ x
                 → v ℕ.∸ x ℕ.+ z ≡ v ℕ.∸ (x ℕ.∸ z)
    v∸x+z≡v∸[x∸z] {z = 0} ℕ.z≤n = DNP.+-identityʳ _
    v∸x+z≡v∸[x∸z] {v} {x} {z = suc z} (ℕ.s≤s s) = begin
      v ℕ.∸ x ℕ.+ suc z ≡⟨ {!!} ⟩
      v ℕ.∸ suc (x ℕ.+ z) ≡⟨ {!!} ⟩
      v ℕ.∸ (x ℕ.∸ suc z) ∎

  takeduv : (x : Buffer)
          → (a b : Buffer.F x)
          → (d : a 𝔽.≤ b)
          → let x₂ = proj₁ $ kanji {x} $ Vimcu a b d in
            (_≡_ on ((𝔽.toℕ a) ↑_ ∘ Buffer.lerpinste)) x x₂
  takeduv x a b d = sym $ begin
    BLT (proj₁ $ kanji {x} $ Vimcu a b d) ≡⟨ refl ⟩
    𝔽.toℕ a ↑ (BLT x ++ BLD x) ≡⟨ refl ⟩
    𝔽.toℕ a ↑ ((𝔽.toℕ a ↑ BL x) ++ BLD x) ≡⟨ teikteik _ _ ⟩
    BLT x ∎
    where
    BL = Buffer.lerpinste
    BLT = (𝔽.toℕ a) ↑_ ∘ BL
    BLD = suc (𝔽.toℕ b) ↓_ ∘ BL
    open ≡-Reasoning
    teikteik : ∀ {a} → {A : Set a}
             → (x : List A)
             → {z : List A}
             → (n : Fin $ length x)
             → let n' = 𝔽.toℕ n in
               n' ↑ (n' ↑ x ++ z) ≡ n' ↑ x
    teikteik (_ ∷ _) 𝔽.zero = refl
    teikteik (_ ∷ _) (𝔽.suc _) = teikteik _ _ ▹ cong (_ ∷_)

  dropyduv : (x : Buffer)
           → (a b : Buffer.F x)
           → (d : a 𝔽.≤ b)
           → let x₂ = proj₁ $ kanji {x} $ Vimcu a b d in
             (_≡_
               (suc (𝔽.toℕ b) ↓ Buffer.lerpinste x)
               (𝔽.toℕ a ↓ Buffer.lerpinste x₂))
  dropyduv x a b d = sym $ begin
    𝔽.toℕ a ↓ BL x₂ ≡⟨ refl ⟩
    a' ↓ (a' ↑ BL x ++ suc b' ↓ BL x) ≡⟨ teikteikdrop (BL x) _ a ⟩
    suc b' ↓ BL x ∎
    where
    a' = 𝔽.toℕ a
    b' = 𝔽.toℕ b
    BL = Buffer.lerpinste
    x₂ = proj₁ $ kanji {x} $ Vimcu a b d
    teikteikdrop : ∀ {a} → {A : Set a}
                 → (x z : List A)
                 → (n : Fin $ length x)
                 → 𝔽.toℕ n ↓ (𝔽.toℕ n ↑ x ++ z) ≡ z
    teikteikdrop (_ ∷ _) _ 𝔽.zero = refl
    teikteikdrop (_ ∷ xs) z (𝔽.suc n) = teikteikdrop xs z n
    open ≡-Reasoning

  module Cusku where
    nilzilcmip : (x : Buffer)
               → (a b : Buffer.F x)
               → (d : a 𝔽.≤ b)
               → let K = proj₂ $ kanji {x} $ Cusku a b d in
                 let L = lines $ from-inj₁ $ from-just K in
                 length L ≡ suc (𝔽.toℕ b ℕ.∸ 𝔽.toℕ a)
    nilzilcmip x a b d = begin
      length L ≡⟨ refl ⟩
      length (lines $ unlines S) ≡⟨ lines∘unlines S ▹ cong length ⟩
      length S ≡⟨ refl ⟩
      length (a' ↓_ $ suc b' ↑ BL) ≡⟨ DLP.length-drop a' _ ⟩
      length (suc b' ↑ BL) ℕ.∸ a' ≡⟨ teiklen BL b ▹ cong (ℕ._∸ a') ⟩
      suc b' ℕ.∸ a' ≡⟨ sukmin d ⟩
      suc (b' ℕ.∸ a') ∎
      where
      a' = 𝔽.toℕ a
      b' = 𝔽.toℕ b
      K = proj₂ $ kanji {x} $ Cusku a b d
      L = lines $ from-inj₁ $ from-just K
      BL = Buffer.lerpinste x
      S = a' ↓_ $ suc b' ↑ BL
      lines∘unlines : (x : List String) → lines (unlines S) ≡ S
      lines∘unlines = {!!}
      open ≡-Reasoning
      sukmin : {m n : ℕ}
             → n ℕ.≤ m
             → suc m ℕ.∸ n ≡ suc (m ℕ.∸ n)
      sukmin ℕ.z≤n = refl
      sukmin (ℕ.s≤s s) = sukmin s
      teiklen : ∀ {a} → {A : Set a}
              → (x : List A)
              → (n : Fin $ length x)
              → length (ℕ.suc (𝔽.toℕ n) ↑ x) ≡ ℕ.suc (𝔽.toℕ n)
      teiklen (_ ∷ _) 𝔽.zero = refl
      teiklen (_ ∷ xs) (𝔽.suc n) = teiklen xs n ▹ cong ℕ.suc

    pindices : (x : Buffer)
             → (a b : Buffer.F x)
             → (d : a 𝔽.≤ b)
             → let K = proj₂ $ kanji {x} $ Cusku a b d in
               let L = lines $ from-inj₁ $ from-just K in
               (n : Fin $ length L)
             → let Lx = Buffer.lerpinste x in
               (Σ
                 (𝔽.toℕ n ℕ.+ 𝔽.toℕ a ℕ.< length Lx)
                 (λ ℓ → L ! n ≡ Lx ! 𝔽.fromℕ< ℓ))
    pindices x a b d n = {!!} , {!!}

  module Basti where
    bindiced : (x : Buffer)
             → (a b : Buffer.F x)
             → (d : a 𝔽.≤ b)
             → let K = proj₂ $ kanji {x} $ Basti a b d in
               (Σ
                 (∃ Buffer.F)
                 (λ (x' , a') →
                   (_×_
                     (𝔽.toℕ a' ≡ {!!})
                     (_≡_
                       (kanji {x} $ Basti a b d)
                       (kanji {x'} $ Jmini a')))))
    bindiced = {!!}

  module Muvgau where
    nilzilcmi : (x : Buffer)
              → (a b c : Buffer.F x)
              → (d : a 𝔽.≤ b)
              → ((_≡_ on (length ∘ Buffer.lerpinste))
                  x
                  (proj₁ $ kanji {x} $ Muvgau a b (just c) d))
    nilzilcmi x a b c d = sym $ begin
      𝓁 (proj₁ K) ≡⟨ {!!} ⟩
      length x'₁ ℕ.+ length x'₂ ℕ.+ length x'₃ ≡⟨ {!!} ⟩
      𝓁 x ∎
      where
      K = kanji {x} $ Muvgau a b (just c) d
      𝓁 = length ∘ Buffer.lerpinste
      x' = Buffer.lerpinste x
      x'₁ = 𝔽.toℕ a ↑ x'
      x'₂ = suc (𝔽.toℕ b) ↓ x'
      x'₃ = 𝔽.toℕ a ↓_ $ suc (𝔽.toℕ b) ↑ x'
      open ≡-Reasoning

    muvipas : (x : Buffer)
            → (a b c : Buffer.F x)
            → (d : a 𝔽.≤ b)
            → ((_≡_ on_ $ 𝔽.toℕ a ↑_ ∘ Buffer.lerpinste)
                x
                (proj₁ $ kanji {x} $ Muvgau a b (just c) d))
    muvipas x a b c d = sym $ begin
      T (BL x') ≡⟨ DLP.take++drop (𝔽.toℕ a) (BL x') ▹ sym ▹ cong T ⟩
      T (T (BL x') ++ D (BL x')) ≡⟨ refl ⟩
      _ ≡⟨ teikteik _ _ ▹_ $ cong $ T ∘ (_++ D (BL x')) ⟩
      T (T (BL x) ++ D (BL x')) ≡⟨ teikteik _ a ⟩
      T (BL x) ∎
      where
      T = 𝔽.toℕ a ↑_
      D = 𝔽.toℕ a ↓_
      BL = Buffer.lerpinste
      x' = proj₁ $ kanji {x} $ Muvgau a b (just c) d
      open ≡-Reasoning
      teikteik : ∀ {a} → {A : Set a}
               → (x : List A)
               → {z : List A}
               → (n : Fin $ length x)
               → let n' = 𝔽.toℕ n in
                 n' ↑ (n' ↑ x ++ z) ≡ n' ↑ x
      teikteik (_ ∷ _) 𝔽.zero = refl
      teikteik (x ∷ xs) (𝔽.suc n) = teikteik xs n ▹ cong (x ∷_)

    muvisez : (x : Buffer)
            → (a b c : Buffer.F x)
            → (d : a 𝔽.≤ b)
            → let n = suc $ 𝔽.toℕ b ℕ.∸ 𝔽.toℕ a in
              let x' = proj₁ $ kanji {x} $ Muvgau a b (just c) d in
              ((_≡_ on n ↑_)
                (𝔽.toℕ a ↓ Buffer.lerpinste x)
                (𝔽.toℕ c ↓ Buffer.lerpinste x'))
    muvisez x a b c d = sym $ begin
      n ↑ (f c ↓ BLT x') ≡⟨ {!!} ⟩
      n ↑ (f a ↓ BLT x) ∎
      where
      f = 𝔽.toℕ
      n = suc $ f b ℕ.∸ f a
      x' = proj₁ $ kanji {x} $ Muvgau a b (just c) d
      BLT = Buffer.lerpinste
      open ≡-Reasoning

    muviros : (x : Buffer)
            → (a b c : Buffer.F x)
            → (d : a 𝔽.≤ b)
            → let x₂ = proj₂ $ kanji {x} $ Muvgau a b (just c) d in
              (_≡_
                ((𝔽.toℕ b) ↓ Buffer.lerpinste x)
                {!!})
    muviros = {!!}

    vimcu : (x : Buffer)
          → (a b c : Buffer.F x)
          → (d : a 𝔽.≤ b)
          → let n = suc (𝔽.toℕ b ℕ.∸ 𝔽.toℕ a) in
            let x' = proj₁ $ kanji {x} $ Muvgau a b (just c) d in
            let L = Buffer.lerpinste in
            (_≡_
              (𝔽.toℕ a ↑ L x ++ suc (𝔽.toℕ b) ↓ L x)
              (𝔽.toℕ c ↑ L x' ++ n ↓ L x'))
    vimcu = {!!}

    muvdusin : (x : Buffer)
             → (a b : Buffer.F x)
             → let R = DFP.≤-reflexive refl in
               let K = kanji {x} $ Muvgau a a (just b) R in
               Data.Maybe.Is-nothing (proj₂ K)
             × let x' = proj₁ K in
               let L = Buffer.lerpinste in
               let e = nilzilcmi x a a b R in
               L x ! a ≡ L x' ! mink a e
             × (_≡_ on ((𝔽.toℕ a ℕ.⊓ 𝔽.toℕ b) ↑_ ∘ L)) x x'
             × (_≡_ on ((𝔽.toℕ a ℕ.⊔ 𝔽.toℕ b) ↓_ ∘ L)) x x'
    muvdusin = {!!}

  module Xruti where
    xrutis : (x : Buffer)
           → (n : Fin $ length $ Buffer.citri x)
           → (_≡_
               (kanji {x} $ Xruti n)
               (let x' = Buffer.citri x ! n in
                (_,_
                  record x {
                    lerpinste = proj₁ x';
                    cablerpinsle = proj₂ x';
                    citri = {!!}}
                  nothing)))
    xrutis = {!!}
\end{code}

\chapter{le skami co'e}

\section{la'oi .\F{readFile}.}
ni'o la'oi .\F{readFile}.\ smimlu ko'a goi la'o zoi.\ \F{IO.Finite.readFile}\ .zoi.\ldots je ku'i cu zmadu ko'a le ka ce'u mapti la'o zoi.\ \datnyveicme{/dev/stdin}\ .zoi.  .i ji'a co'e co mu'oi zoi.\ \F{𝕊.lines}\ .zoi.

\begin{code}
readFile : String → IO $ List String
readFile x = if (x ≡ᵇ "/dev/stdin") (IO.lift stdin) generic
  where
  generic = 𝕊.lines IO.<$> IO.Finite.readFile x
  postulate stdin : ABIO.IO $ List String
  {-# FOREIGN GHC import Data.Bool #-}
  {-# FOREIGN GHC import Data.Text #-}
  {-# FOREIGN GHC import System.IO #-}
  {-# COMPILE GHC
      stdin = const $ stdin' []
      where {
        stdin' :: [Data.Text.Text] -> IO [Data.Text.Text];
        stdin' x = isEOF >>= bool getLine' (return x)
        where {
          getLine' :: IO [Data.Text.Text];
          getLine' = getLine >>= f . Data.Text.pack
          where {
            f "." = return x;
            f n = stdin' $ x ++ [n]}}} #-}
\end{code}

\section{la'o zoi.\ \F{\AgdaUnderscore{}<=<ᵢₒ\AgdaUnderscore{}}\ .zoi.}
ni'o la .varik. na jinvi le du'u sarcu lo nu jimpe kei fa fa lo nu vo'a ciksi fo lo lojbo

\begin{code}
_<=<ᵢₒ_ : ∀ {a}
        → {A B C : Set a}
        → (B → IO C)
        → (A → IO B)
        → A
        → IO C
_<=<ᵢₒ_ g = _∘_ $ IO._>>= g
\end{code}

\section{la'oi .\F{main}.}
ni'o zabna ciksi la'oi .\F{main}.\ fo ma bau la .lojban.

\begin{code}
{-# NON_TERMINATING #-}
main : Main
main = run $ IO.lift snurytcati IO.>> getArgs IO.>>= uic ∘ 𝕃.head
  where
  postulate snurytcati : ABIO.IO ABU.⊤
  {-# FOREIGN GHC import System.OpenBSD.Plegg #-}
  {-#
      COMPILE GHC
      snurytcati = plegg [CPath, RPath, WPath, Stdio]
  #-}
  uic : Maybe String → IO ⊤
  uic = ⟲ <=<ᵢₒ maybe mkDef (IO.pure def)
    where
    def = record {
      datnyveicme = nothing;
      lerpinste = "" ∷ List.[];
      cablerpinsle = 𝔽.zero;
      citri = List.[];
      rejgaudatni = nothing
      }
    mkDef : _
    mkDef c = uit c IO.<$> readFile c
      where
      uit : _ → _ → _
      uit c [] = record def {datnyveicme = just c}
      uit c x@(_ ∷ _) = record {
        datnyveicme = just c;
        lerpinste = x;
        cablerpinsle = 𝔽.opposite 𝔽.zero;
        citri = 𝕃.[];
        rejgaudatni = just c
        }
    ⟲ : Buffer → IO ⊤
    ⟲ x = IO.getLine IO.>>= f ∘ reed x
      where
      f : Maybe $ Cmd x → IO ⊤
      f nothing = IO.putStrLn "?" IO.>> ⟲ x
      f (just c) with kanji c
      ... | x' , nothing = ⟲ x'
      ... | x' , just (inj₁ z) = IO.putStrLn z IO.>> ⟲ x'
      ... | x' , just (inj₂ z) with z
      ... | Sisti!ᵢₒ = IO.pure _
      ... | Skamiᵢₒ a = {!!}
      ... | Tciduᵢₒ a b = readFile a IO.>>= ⟲ ∘ J x' b
        where
        J : (x : Buffer)
          → (n : Maybe $ Buffer.F x)
          → (s : List String)
          → Buffer
        J x n s = record x {
          citri = Buffer.cninycitri x;
          lerpinste = insert (BL x) s n;
          cablerpinsle = {!!}}
          where
          BL = Buffer.lerpinste
      ... | Rejgauᵢₒ a b = IO.writeFile b a IO.>> ⟲ x''
        where
        x'' = record x {rejgaudatni = just {!!}}
      ... | Sistiᵢₒ = f $ mapₘ (λ _ → Sisti!) $ decToMaybe $ r ≟ c₁
        where
        r = Buffer.rejgaudatni x'
        c₁ = mapₘ (unlines ∘ proj₁) $ 𝕃.head $ Buffer.citri x'
\end{code}
\end{document}
