
\usepackage{mathtools}
\DeclarePairedDelimiter\ceil{\lceil}{\rceil}
\DeclarePairedDelimiter\floor{\lfloor}{\rfloor}
\newcommand{\dcup}{\;\dot\cup\;}
\newcommand\eqdef{\triangleq}
\newcommand\empset{\{\}}
\newcommand{\cd}[1]{#1^{\flat}}
\newcommand{\ad}[1]{#1^{\sharp}}
\newcommand{\interpret}[1]{\llbracket #1 \rrbracket}
\newcommand{\adi}[1]{\interpret{#1}}
\newcommand{\cdi}[1]{\cd{\interpret{#1}}}
\newcommand{\aadi}[1]{\ad{\interpret{#1}}}
\newcommand{\audi}[1]{\interpret{#1}_\downarrow}
\newcommand{\aodi}[1]{\interpret{#1}_\uparrow}
\newcommand{\esem}[2]{\mathcal{E}^{#1}\interpret{#2}}
\newcommand{\dsem}[2]{\mathcal{D}^{#1}\interpret{#2}}
\newcommand{\sem}[2]{\mathcal{S}^{#1}\interpret{#2}}
\newcommand{\csem}[2]{\mathcal{C}^{#1}\interpret{#2}}
\newcommand{\tsem}[2]{\mathcal{T}^{#1}\interpret{#2}}
\newcommand{\isem}[2]{\mathcal{I}^{#1}\interpret{#2}}
\newcommand{\embed}[3]{\mathit{embed}(#1, #2, #3)}
\newcommand{\project}[2]{#1(#2)}
\newcommand{\pff}[2]{#1 \nrightarrow #2}
\newcommand{\pf}[2]{[\pff{#1}{#2}]}
\newcommand{\tf}[2]{[#1 \to #2]}
\newcommand{\pgamma}{\hat{\gamma}}
\newcommand{\fpowerset}{\mathcal{P}_{\mathit{f}}}
\newcommand{\powerset}{\mathcal{P}}
\newcommand{\substitution}[2]{[#1 \mapsto #2]}

\newcommand{\llm}{\textcolor{gray}{\raisebox{0.1ex}{\scriptsize\faRobot}}}

\newcounter{rocqcounter}
\newcommand{\autorocq}{\stepcounter{rocqcounter}\texttt{[\llm\,\therocqcounter]}}

\newcommand{\tifq}{%
  \begin{tikzpicture}[baseline={(0,0.02)}]
    \draw (0,0) circle (0.03); % bottom circle
    \draw (0,0.05) -- (0,0.1); % vertical line
    \draw (0,0.1) .. controls (0.25,0.22) and (-0.05, 0.4) .. (-0.07,0.15); % upper arc
  \end{tikzpicture}%
}

\newcommand{\tifdotdot}{%
  \begin{tikzpicture}
    \draw (0,0) circle (0.03); % bottom circle
    \draw (0,0.1) circle (0.03); % bottom circle
  \end{tikzpicture}%
}

\newcommand{\tifbar}{%
  \begin{tikzpicture}[baseline={(0,0.07)}]
    \draw (0,0) -- (0,0.35);
    \draw (0.05,0) -- (0.05,0.35);
    \draw (0,0) -- (0.05,0);
    \draw (0,0.35) -- (0.05,0.35);
  \end{tikzpicture}%
}

\newcommand{\tif}[3]{\llparenthesis~ #1 ~\tifq #2 ~\tifdotdot~ #3 ~\rrparenthesis}
\newcommand{\tifbegin}[2]{\llparenthesis~ #1 ~\tifq #2}
\newcommand{\tifcase}[2]{\,\tifbar~ #1 ~\tifq #2}
\newcommand{\tifend}[1]{\,\tifdotdot~ #1 ~\rrparenthesis}


\newcommand{\isbot}[1]{\mathit{isbot}([#1])}
\newcommand{\isbotd}[1]{\mathit{isbot}(#1)}
\newcommand{\isbotx}[1]{\mathit{isbot}_\times(#1)}
\newcommand{\isboti}[1]{\mathit{isbot}_\mathbf{I}(#1)}
\newcommand{\splitjoin}{\mathit{splitjoin}}
\newcommand{\sqcupbot}{\mathbin{\underline{\sqcup}}}

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{example}[theorem]{Example}

\begin{document}

\section{Abstract Satisfaction}

\textit{Abstract interpretation} is a framework for the sound analysis of computer programs by over-approximation of their semantics~\cite{cousot2021principles,cousot-abstract-1977}.
\textit{Abstract satisfaction} is the generalization of constraint solving to abstract interpretation.
It is studied in, for instance,~\cite{gotlieb:hal-00807856,pelleau-constraint-2013,dsilva-abstract-2014,TPLP2020-Talbot} but a similar treatment was already used in~\cite{benhamou-heterogeneous-1996} for mixed constraint solving.
% In particular, a more general view of propagators stems from abstract interpretation, where propagators are viewed as monotone functions over lattice structures approximating the set of solutions.
As our work is relevant to both the abstract interpretation and constraint programming communities, we place ourselves in the framework of abstract satisfaction which intersects both.
To keep the paper accessible to both communities, it is self-contained and we bridge the terminologies when it is useful.

In the following, we consider constraint programming over integer variables only.
Let $X$ be a finite set of variables.
For the purposes of this paper, the constraints under consideration are of the shape $x = y \odot z$ where $\odot \in \mathbf{OP} = \{+,-,\cdot,\textnormal{fdiv},\textnormal{cdiv},\textnormal{tdiv},\textnormal{ediv}\}$.
We denote by $\mathbf{C}$ the set of all such constraints.
In particular, we consider four division operations: the floor ($\textnormal{fdiv}$), ceiling ($\textnormal{cdiv}$), truncated ($\textnormal{tdiv}$) and Euclidean ($\textnormal{ediv}$) division operations.
For each constraint $c \in \mathbf{C}$, let $\mathit{scp}(c) \subseteq X$ be the set of free variables of $c$, called its \textit{scope}---for instance, $\mathit{scp}(x = \textnormal{tdiv}(y,z)) = \{x, y, z\}$\footnote{For division operations, we write $\textnormal{tdiv}(y,z)$ instead of $y~\textnormal{tdiv}~z$.}.
An \textit{assignment} is a map $\mathit{asn}\in X \to \mathbb{Z}$, and we denote the set of all assignments by $\mathbf{Asn}$.
We equip the set of subsets of assignments with the order induced by inclusion $\langle \powerset(\mathbf{Asn}), \subseteq \rangle$ and call it the \textit{concrete domain}.
The set of solutions of each constraint is given by the function $\mathit{rel} \in \mathbf{C} \to \mathcal{P}(\mathbf{Asn})$ defined as follows:
\begin{displaymath}
\begin{array}{l}
\mathit{rel}(x = y + z) \eqdef \{ a \in \mathbf{Asn} \;|\; a(x) = a(y) + a(z) \} \\
\mathit{rel}(x = y - z) \eqdef \{ a \in \mathbf{Asn} \;|\; a(x) = a(y) - a(z) \} \\
\mathit{rel}(x = y \cdot z) \eqdef \{ a \in \mathbf{Asn} \;|\; a(x) = a(y) \cdot a(z) \} \\
\mathit{rel}(x=\textnormal{fdiv}(y,z)) \eqdef \{a \in \mathbf{Asn'} \;|\; a(x) = \lfloor\frac{a(y)}{a(z)}\rfloor \} \\
\mathit{rel}(x=\textnormal{cdiv}(y,z)) \eqdef \{a \in \mathbf{Asn'} \;|\; a(x) = \lceil\frac{a(y)}{a(z)}\rceil \}\\[0.1cm]
\mathit{rel}(x=\textnormal{tdiv}(y,z)) \eqdef \\
\qquad \{a \in \mathbf{Asn'} \;|\;
x=\begin{cases}
    \lfloor\frac{a(y)}{a(z)}\rfloor&\text{if }\frac{a(y)}{a(z)}\geq 0\\
    \lceil\frac{a(y)}{a(z)}\rceil&\text{if }\frac{a(y)}{a(z)}< 0\\
\end{cases}\}\\[0.2cm]
\mathit{rel}(x=\textnormal{ediv}(y,z)) \eqdef \\
\qquad \{a \in \mathbf{Asn'} \;|\;
x=\begin{cases}
    \lfloor\frac{a(y)}{a(z)}\rfloor&\text{if }a(z)> 0\\
    \lceil\frac{a(y)}{a(z)}\rceil&\text{if }a(z)< 0\\
\end{cases} \}
\end{array}
\end{displaymath}
\noindent
where $\mathbf{Asn'} = \{a \in \mathbf{Asn} \;|\; a(z) \neq 0\}$, $\frac{y}{z}$ is the division in the real numbers, $\lfloor . \rfloor \in \mathbb{R} \to \mathbb{Z}$ is the floor function and $\lceil . \rceil \in \mathbb{R} \to \mathbb{Z}$ the ceiling function.
For efficiency, the four division functions can be implemented without relying on floating-point arithmetic using truncated integer division as shown in~\cite{leijen-division-2001}.

Given a constraint $c$, its \textit{concrete propagator} is a function $\sem{}{c} \in \powerset(\mathbf{Asn}) \to \powerset(\mathbf{Asn})$ defined as $\sem{}{c}P \eqdef P \cap \mathit{rel}(c)$.
For example, given $P = \{\{x \mapsto 0, y \mapsto 0, z \mapsto 0\}, \{x \mapsto 1, y \mapsto 1, z \mapsto 1\}\}$, we have $\sem{}{x = y + z}P = \{\{x \mapsto 0, y \mapsto 0, z \mapsto 0\}\}$; the unsatisfiable assignments are filtered out.
The collection of functions $\sem{}{.}$ are \textit{closure operators}: they are idempotent ($\sem{}{c}(\sem{}{c}P) = \sem{}{c}P$), monotone ($P \subseteq P' \Rightarrow \sem{}{c}P \subseteq \sem{}{c}P'$) and reductive ($\sem{}{c}P \subseteq P$) for all $c \in \mathbf{C}$ and $P,P' \in \mathcal{P}(\mathbf{Asn})$.
The set of solutions of a set of constraints $\{c_1,\ldots,c_n\}$ is given by the greatest fixpoint $\mathbf{gfp}~\sem{}{c_1} \circ \ldots \circ \sem{}{c_n}$.
Note that because each constraint removes all unsatisfiable assignments, we reach the fixpoint after one iteration, that is, the composition $\sem{}{c_1} \circ \ldots \circ \sem{}{c_n}$ is itself a closure operator \autorocq{} (but this is not a generally true property of closure operators).

As enumerating all possible assignments is not an efficient procedure---or even possible in case of infinite domains---we rely on abstractions of the concrete domain $\mathcal{P}(\mathbf{Asn})$.
An \emph{abstract domain} $\langle A, \leq \rangle$ is a lattice approximating the concrete domain.
By abuse of notation, we will sometimes refer to a lattice $\langle A, \leq \rangle$ simply as $A$, leaving the order implicit.
The approximation is formally defined by a Galois connection $\powerset(\mathbf{Asn}) \galois{\alpha}{\gamma} A$, where $\alpha \in \powerset(\mathbf{Asn}) \to A$ is called the \emph{abstraction function} and $\gamma \in A \to\powerset(\mathbf{Asn})$ the \emph{concretization function}.
The pair $\langle \alpha, \gamma \rangle$ is a Galois connection iff $\forall{P \in \powerset(\mathbf{Asn})},~\forall{\overline{P} \in A},~\alpha(P) \leq \overline{P} \Leftrightarrow P \subseteq \gamma(\overline{P})$.
Although Galois connections are rarely explicitly mentioned in constraint programming literature, as we show next, various local consistency conditions are actually induced by Galois connections.
% In the following, we consider the Cartesian and interval abstractions over-approximating the concrete domain $\mathcal{P}(\mathbf{Asn})$.

\subsection{Cartesian Abstraction}

In constraint programming, it is frequent to directly define a discrete constraint network using a Cartesian abstraction of the variable's domains.
A \textit{constraint network} is a pair $\langle d, C \rangle$ such that $d \in X \to \mathcal{P}(\mathbb{Z})$ is the \textit{domain function} and $C \subseteq \mathbf{C}$ a finite set of constraints.
The set of solutions of a constraint network is:
\begin{displaymath}
\begin{array}{l}
% \mathit{sol} \in (\mathbf{D} \times \mathcal{P}(\mathbf{C})) \to \mathcal{P}(\mathbf{Asn}) \\
\mathit{sol}(d, C) \eqdef \{\mathit{asn} \in \mathbf{Asn} \;|\; \\
\quad \forall{c \in C},~\mathit{asn} \in \mathit{rel}(c) \land \forall{x \in X},~\mathit{asn}(x) \in d(x)\}
\end{array}
\end{displaymath}
\noindent
A domain function is \textit{failed} if at least one variable has an empty domain.
We consider failed domain functions as equivalent:
\begin{displaymath}
\begin{array}{l}
\isbotx{d} \eqdef \exists{x \in X},~d(x) = \{\}\\[0.1cm]
d \sim_\times d' \eqdef (\isbotx{d} \land \isbotx{d'}) \lor d = d'
\end{array}
\end{displaymath}
\noindent
The structure $\mathbf{D} = \langle (X \to \mathcal{P}(\mathbb{Z}))/ {\sim_\times}, \leq \rangle$ is a complete lattice where the order is defined pointwise with care for the bottom equivalence class ($d \leq d' \eqdef \isbotx{d} \lor \forall{x \in X},~d(x) \subseteq d'(x)$) \autorocq{}.
The lattice $\mathbf{D}$ is a Cartesian abstraction of $\powerset(\mathbf{Asn})$, and the abstract and concrete domains are connected by the Galois connection $\powerset(\mathbf{Asn}) \galois{\alpha_\times}{\gamma_\times} \mathbf{D}$ defined as:
\begin{displaymath}
\begin{array}{l}
\alpha_\times(P) \eqdef x \in X \mapsto \{\mathit{asn}(x) \;|\; \mathit{asn} \in P\} \\
\gamma_\times(\overline{P}) \eqdef \{ \mathit{asn} \in \mathbf{Asn} \;|\; \forall{x \in X}, \mathit{asn}(x) \in \overline{P}(x) \}
\end{array}
\end{displaymath}
The pair $\langle \alpha_\times, \gamma_\times \rangle$ is a Galois connection\autorocq{}.
For each constraint $c$, we can leverage this Galois connection to obtain a propagator function $\sem{\times}{c} \in \mathbf{D} \to \mathbf{D} \eqdef \alpha_\times \circ \sem{}{c} \circ \gamma_\times$ over-approximating the concrete propagator $\sem{}{c}$.
In constraint programming, the propagators $\sem{}{.}$ are exactly the ones enforcing generalized arc consistency (GAC) as shown in~\cite{gotlieb:hal-00807856,pelleau-constraint-2013}.
This definition with Galois connection entails $\sem{\times}{c}$ is the best propagator one can hope for the constraint $c$; and indeed, GAC is the strongest consistency when considering constraints individually.
However, in practice, the functions $\alpha_\times$ and $\gamma_\times$ are impractical, and the goal is to implement a propagator $p_c$ equivalent to $\sem{\times}{c}$ without relying on those.
\begin{example} The following function $\sem{\times'}{x = y \cdot z} \in \mathbf{D} \to \mathbf{D}$ is a Cartesian propagator for the multiplication constraint:
\begin{displaymath}
\begin{array}{l}
\sem{\times'}{x = y \cdot z}d \eqdef d[x \mapsto X, y \mapsto Y, z \mapsto Z]\\
\quad X = \{a \in d(x) \;|\; \exists{b \in d(y)},~\exists{c \in d(z)},~a = b \cdot c\} \\
\quad Y = \{b \in d(y) \;|\; \exists{a \in d(x)},~\exists{c \in d(z)},~a = b \cdot c\} \\
\quad Z = \{c \in d(z) \;|\; \exists{a \in d(x)},~\exists{b \in d(y)},~a = b \cdot c\}
\end{array}
\end{displaymath}
\noindent
The time complexity of $\sem{\times'}{x = y \cdot z}$ is better than $\sem{\times}{x = y \cdot z}$ which enumerates all the assignments with $\gamma_\times$.
Autoformalization is a powerful tool to show both are equivalent \autorocq{}.
Further improvements could also be automatically proven equivalent.
\end{example}
To improve efficiency, it is not always possible to preserve equivalence w.r.t. $\sem{\times}{.}$.
However, non-equivalent propagators must preserve \textit{soundness}: they must not discard solutions of the constraint implemented.
More formally, we compare the strength of propagators $p,p' \in A \to A$ using the pointwise order $p~\dot{\leq}~p' \eqdef \forall{a \in A},~p(a) \leq p'(a)$ indicating that $p$ is stronger than $p'$.
A propagator $p_c$ implementing a constraint $c$ is sound whenever $\sem{\times}{c}~\dot{\leq}~p_c$.
In more general terms, given a Galois connection $\mathcal{P}(\mathbf{Asn}) \galois{\alpha}{\gamma} A$ and a constraint $c$, a propagator $p_c \in A \to A$ is sound\footnote{In abstract interpretation, this definition of soundness was already defined in~\cite{cousot-systematic-1979}, and $\alpha \circ \sem{}{c} \circ \gamma$ was called ``best correct upper approximation''.} iff:
\begin{displaymath}
\alpha \circ \sem{}{c} \circ \gamma~\dot{\leq}~p_c \tag*{\text{(soundness)}}
\end{displaymath}
We call the reverse inclusion \textit{abstract completeness}:
\begin{displaymath}
\alpha \circ \sem{}{c} \circ \gamma~\dot{\geq}~p_c \tag*{\text{($\alpha$-completeness)}}
\end{displaymath}
This property does not guarantee the propagator extracts a solution of the constraint $c$ as the abstraction function $\alpha$ might introduce over-approximation\footnote{We call ``concrete completeness'' the property $\sem{}{c}~\dot{\supseteq}~\gamma \circ p_c \circ \alpha$ which guarantees the propagator generates an under-approximation of the solution space. It is notably used for inner test in continuous constraint solving~\cite{granvilliers-realpaver:-2006}.}.
A propagator that is sound and $\alpha$-complete is called the \textit{best propagator}.
If $\alpha$-completeness is not satisfied, a propagator is typically required to be the best on assignments:
\begin{displaymath}
(\alpha \circ \sem{}{c} \circ \gamma)a = (p_c)a \tag*{\text{(best on assignment)}}
\end{displaymath}
for all $a \in A, \mathit{asn} \in \mathbf{Asn}$ where $\gamma(a) = \{\mathit{asn}\}$.
This property is called ``checking'' in~\cite{schulte-efficient-2008}.
Additional properties of propagators include reductivity, monotonicity and idempotency, see e.g.~\cite{saraswat-semantic-1991,apt-essence-1999,schulte-tack-weakly-prop-2009}.
In particular, GAC propagators have all three properties as shown by the following proposition.
\begin{proposition}
For any Galois connection $A \galois{\alpha}{\gamma} B$, if $f \in A \to A$ is a closure operator, then so is $\alpha \circ f \circ \gamma$ \autorocq{}.
\label{galois-closure-proposition}
\end{proposition}
\noindent
Since $\sem{}{c}$ is a closure operator, so is $\sem{\times}{c}$.
As a corollary, proving a propagator $p_c$ to be the best is sufficient to prove it is also a closure operator.

So far, we have considered propagators individually, but all definitions can be lifted to constraint networks.
In particular, constraint propagation is the computation of the greatest fixpoint defined as $\mathit{prop}(d, \{c_1,\ldots,c_n\}) \eqdef \mathbf{gfp}_d~\sem{\times}{c_1} \circ \ldots \circ \sem{\times}{c_n}$ where $\mathbf{gfp}_d~f \eqdef \mathbf{gfp}~f \circ \lambda x.d$, that is, the greatest fixpoint of $f$ below $d$.
The functional composition of monotone and sound propagators is sound \autorocq{}: this is important as it means it suffices to prove soundness independently on each propagator.
Monotonicity and reductivity are also preserved by composition, which guarantee the existence of the greatest fixpoint on complete lattices (Tarski theorem).
As long as the propagators are executed fairly, their greatest mutual fixpoint is the same for every order of execution~\cite{cousot-asynchronous-1977,apt-essence-1999}\autorocq{}.
This fact has been used to design various \textit{propagation algorithms} to accelerate the computation of the fixpoint~\cite{schulte-efficient-2008,propagation-guido-tack-2009}.
% As constraint propagation is sound but incomplete in general, it must be interleaved with a search procedure.
% In this paper, we solely focus on propagators and point the readers to e.g.~\cite{lecoutre-constraint-2009,propagation-guido-tack-2009} for a complete presentation of the solving algorithm.

\section{Interval Abstract Domain}
\label{sec-itv-ad}

The abstraction $\mathbf{D}$ can be too costly for large domains or even incomputable for infinite domains.
In exchange for a loss in precision, the interval abstract domain $\mathbf{I}$ offers very efficient propagators and a lightweight memory footprint (usually just two integers).
Our definition is slightly different than the one commonly found (e.g.~\cite{cousot2021principles,mine-tutorial-2017}) as we also allow for any pair of integers $(\ell,u)$ such that $\ell > u$; we call \emph{empty} any such interval.
If we restrict the abstract domain to non-empty intervals with a special element $\bot$, the result of every interval operation needs to be normalized by a function\footnote{$\tif{b}{X}{Y}$ returns $X$ if the expression $b$ is true and $Y$ otherwise.} $\mathit{itv}(\ell, u) \eqdef \tif{\ell > u}{\bot}{[\ell,u]}$, which allows for a discrepancy between theory (only one representation of an empty interval) and practice (multiple representations).
Practical implementations do not always normalize, but it leads to unwarranted overapproximation in the join operation, which we rely on to obtain propagators for the integer division constraints.
In addition, we allow for infinite bounds, which is not often supported in discrete constraint solvers.

Let $\mathbb{Z}^{\infty} \eqdef \mathbb{Z} \cup \{-\infty,\infty\}$ and $I = \mathbb{Z}^{\infty} \times \mathbb{Z}^{\infty}$ the set of intervals.
The following operations are standard on intervals:
\begin{itemize}
\item $[a,b] \preceq [c,d] \eqdef a \geq c \land b \leq d$,
\item $[a,b] \curlyvee [c,d] \eqdef[\min\{a,c\}, \max\{b,d\}]$,
\item $[a,b] \curlywedge [c,d] \eqdef [\max\{a,c\}, \min\{b,d\}]$,
\end{itemize}
The structure $\langle I, \preceq, \curlyvee, \curlywedge \rangle$ is a lattice \autorocq{}.
The meet operation behaves as expected in the presence of empty intervals.
This is not the case of the join operation which may return a non-empty interval even if both inputs are empty.
For example, $[2,1] \curlyvee [1,0]=[1, 1]$, which unnecessarily overapproximates the result that should represent an empty interval.
Moreover, if only one input is empty, the join may still introduce an unnecessary overapproximation, e.g. $[1,0]\curlyvee[2,3]=[1,3]$.
The order is also suboptimal as $[1,0]$ and $[\infty,-\infty]$ are incomparable although they both represent an empty set.

To remediate this situation, we rely on the predicate $\mathit{isbot} \in I \to \{\mathit{true},\mathit{false}\}$ to classify empty and non-empty intervals: $\isbot{\ell,u} \eqdef (\ell > u \lor \ell = \infty \lor u = -\infty)$.
It can be used to define the equivalence relation $\sim \subseteq I \times I$:
\begin{displaymath}
[a,b] \sim [c,d] \eqdef (\isbot{a,b} \land \isbot{c, d}) \lor [a,b]=[c,d]
\end{displaymath}
The lattice $\widetilde{I} = \langle I/{\sim}, \sqsubseteq, \sqcup, \sqcap \rangle$ views all empty intervals as equivalent and is defined as:
\begin{displaymath}
\begin{array}{l}
[a,b] \sqsubseteq [c,d] \eqdef \isbot{a,b} \lor (a \geq c \land b \leq d) \\[0.2cm]
[a,b] \sqcup [c,d] \eqdef \tifbegin{\isbot{a,b}}{[c,d]}\\
\;\phantom{[a,b] \sqcup [c,d] \eqdef }\tifcase{\isbot{c,d}}{[a,b]} \\
\;\phantom{[a,b] \sqcup [c,d] \eqdef }\tifend{[a,b] \curlyvee [c,d]}\\[0.2cm]
[a,b] \sqcap [c,d] \eqdef [a,b] \curlywedge [c,d]\\
\end{array}
\end{displaymath}
Further, it is a complete lattice \autorocq{} with a top element $\top = [-\infty, \infty]$ representing the largest interval, and a bottom element $\bot$ which can be represented by any empty interval.
We use $[\infty, -\infty]$ as the representative element of the equivalence class of empty intervals.
There is a Galois connection $\mathcal{P}(\mathbb{Z}) \galois{\alpha_i}{\gamma_i} \widetilde{I}$ defined by:
\begin{displaymath}
\begin{array}{l}
  \alpha_i(S) \eqdef [\inf S, \sup S] \quad
  \gamma_i([\ell, u]) \eqdef \{v \in \mathbb{Z} \;|\; \ell \leq v \leq u\}
\end{array}
\end{displaymath}
Recall that $\inf(\empset)=\infty$ and $\sup(\empset)=-\infty$. Moreover, $\inf S=\min S$ if $S$ is a lower-bounded set and $\inf S=-\infty$ otherwise; similarly $\sup S=\max S$ if $S$ is an upper-bounded set and $\max S=\infty$ otherwise.
The pair $\langle \alpha_i, \gamma_i \rangle$ is a Galois connection \autorocq{}.

We lift the interval lattice $\widetilde{I}$ to domain functions $X \to \widetilde{I}$ in order to represent the domain of each variable.
Similarly to $\mathbf{D}$, we have an equivalence class of failed domain functions:
\begin{displaymath}
\begin{array}{l}
\isboti{d} \eqdef \exists{x \in X},~\mathit{isbot}(d(x))\\[0.1cm]
d \sim_\mathbf{I} d' \eqdef (\isboti{d} \land \isboti{d'}) \lor d = d'
\end{array}
\end{displaymath}
\noindent
The interval abstract domain is a lattice $\mathbf{I} = \langle (X \to \widetilde{I})/ {\sim_\mathbf{I}}, \dot{\sqsubseteq}, \dot{\sqcup}, \dot{\sqcap} \rangle$ where all operations are lifted pointwise from $\widetilde{I}$ with special care for the bottom equivalence class.
\begin{displaymath}
\begin{array}{l}
d \mathbin{\dot{\sqsubseteq}} d' \eqdef \isboti{d} \lor \forall{x \in X},~d(x) \leq d'(x) \\[0.2cm]
d \mathbin{\dot{\sqcup}} d' \eqdef \tifbegin{\isboti{d}}{d'}\\
\;\phantom{d \sqcup d' \eqdef }\tifcase{\isboti{d'}}{d} \\
\;\phantom{d \sqcup d' \eqdef }\tifend{x \in X \mapsto d(x) \sqcup d'(x)}\\[0.2cm]
d \mathbin{\dot{\sqcap}} d' \eqdef x \in X \mapsto d(x) \sqcap d'(x)\\
\end{array}
\end{displaymath}
$\mathbf{I}$ is a complete lattice~\autorocq{}.
\noindent
The Galois connection $\mathbf{D} \galois{\alpha_\mathbf{I}} {\gamma_\mathbf{I}}\mathbf{I}$ formally shows the abstraction $\mathbf{I}$ is overapproximating $\mathbf{D}$:
\begin{displaymath}
  \begin{array}{l}
  \alpha_\mathbf{I}(P) \eqdef x \in X \mapsto \alpha_i(P(x)) \\
  \gamma_\mathbf{I}(\overline{P}) \eqdef x \in X \mapsto \gamma_i(\overline{P}(x))
  \end{array}
\end{displaymath}
\noindent
The pair $\langle \alpha_\mathbf{I}, \gamma_\mathbf{I} \rangle$ is a Galois connection \autorocq{}.

\section{Interval Bound Propagation}

\begin{table}[t]
\begin{center}
\begin{tabular}{l|llll}
\toprule
 & \multicolumn{4}{|c}{\textbf{Subintervals of $[-15, 15]$}} \\
 & \multicolumn{4}{|c}{\textbf{(total: $122.023.936$)}} \\
 \midrule
\textbf{Solvers} & \textbf{fdiv} & \textbf{cdiv} & \textbf{tdiv} & \textbf{ediv} \\
\midrule
Gecode & \xmark & \xmark & $80.12\%$ & \xmark \\
Choco & \xmark & \xmark & $69.36\%$ & \xmark \\
SWI-prolog & $76.83\%$ & $76.83\%$ & $78.07\%$ & \xmark \\
Eclipse & \xmark & \xmark & $94.49\%$ & \xmark \\
Apron & $36.42\%$ & $36.42\%$ & $34.67\%$ & \xmark \\
\midrule
$\isem{\mathbb{R}}{.}$ & $71.63\%$ & $71.63\%$ & $65.86\%$ & $69.31\%$ \\
% The next line splits on the denominator z.
% $\isem{\mathbb{R}+}{.} ~\ddot{\sqcup}~ \isem{\mathbb{R}-}{.}$ & $76.04\%$ & $76.04\%$ & $71.17\%$ & $75.91\%$ \\
$\isem{}{.}$ & $\mathbf{100\%}$ & $\mathbf{100\%}$ & $\mathbf{100\%}$ & $\mathbf{100\%}$ \\
\bottomrule
\end{tabular}
\end{center}
\caption{Percentage of combinations on which each system reaches the best possible propagation. The symbol \xmark{} indicates the lack of support for a particular division. We test all combinations of non-empty sub-intervals of $[-15, 15] \in I$ for $x,y,z$.}
\label{table-compare-overall}
\end{table}

Our goal is to define a collection of (best) sound propagators $\isem{}{x = y \odot z}$ for each operator $\odot \in \mathbf{OP}$.
The best interval propagator for any constraint $c$ is defined as:
\begin{displaymath}
\isem{}{c} \eqdef \alpha_\mathbf{I} \circ \sem{\times}{c} \circ \gamma_\mathbf{I}
\end{displaymath}
Importantly, the properties of $\sem{\times}{c}$ extends compositionally to $\isem{}{c}$, which means we do not need to prove $\isem{}{c}$ w.r.t. the concrete domain, but w.r.t. the simpler Cartesian abstraction.
\begin{theorem}[Soundness commutation \autorocq{}]
Let $\langle \mathcal{P}(\mathbf{Asn}), \subseteq \rangle \galois{\alpha}{\gamma} \langle A, \leq \rangle \galois{\alpha'}{\gamma'} \langle B, \sqsubseteq \rangle$ be successive abstractions of the concrete domain and $\sem{A}{.} \in A \to A$ and $\sem{B}{.} \in B \to B$.
Then, for every constraint $c$, if we have:
\begin{displaymath}
\alpha \circ \sem{}{c} \circ \gamma~\dot{\leq}~\sem{A}{.} \textnormal{ and } \alpha' \circ \sem{A}{c} \circ \gamma'~\dot{\sqsubseteq}~\sem{B}{.}
\end{displaymath}
then
\begin{displaymath}
\alpha' \circ \alpha \circ \sem{}{c} \circ \gamma \circ \gamma'~\dot{\sqsubseteq}~\sem{B}{.}
\end{displaymath}
\end{theorem}
\noindent
A corollary that the best and best on assignment properties also commute: since we have $\dot{\sqsubseteq}$, it also covers $=$ \autorocq{}.
Those observations indicate that whenever we can prove $\sem{\times}{c} = \isem{}{c}$, we also prove $\isem{}{c}$ is a closure operator for free (by Proposition~\ref{galois-closure-proposition}).
% LLMs can sometimes take the long road to prove some properties which might be consequences of simpler theorems.

Similarly to $\langle \alpha_\times, \gamma_\times \rangle$ which induces GAC, $\langle \alpha_\mathbf{I}, \gamma_\mathbf{I} \rangle$ induces bounds($\mathbb{Z}$) consistency~\cite{schulte-bound-domain-same-2005}.
A sound and reductive propagator $p_c \in \mathbf{I} \to \mathbf{I}$ enforces bounds($\mathbb{Z}$) consistency on a constraint $c$ iff for all $x \in X$ and $v \in \{l,u\}$ for $[l,u] = p_c(d)(x)$, there exists $\mathit{asn} \in rel(c)$ such that $\mathit{asn}(x) = v \land \forall{y \in X},~\mathit{asn}(y) \in p_c(d)(y)$.
As shown in~\cite{gotlieb:hal-00807856,pelleau-constraint-2013}, a propagator $p_c$ enforces bounds($\mathbb{Z}$) iff $p_c = \isem{}{c}$ (on bounded intervals as bounds($\mathbb{Z}$) consistency is not defined for infinite intervals) \autorocq{}.

We now define interval propagators for the different constraints.
In order to make the algorithms more concise, we rely on the operator $d(x) \leftarrow E$ which updates the domain of $x$ with the result of the expression $E$ and returns from the current control flow if the updated interval is empty.
It is desugared to:
\begin{displaymath}
d(x) \leftarrow E \eqdef
\begin{array}{l}
d(x) = d(x) \sqcap E \\
\textbf{if } \isbotd{d(x)} \textbf{ then return } d
\end{array}
\end{displaymath}
We also compose propagators by pointwise join as follows: given $p, p' \in \mathbf{I} \to \mathbf{I}$, $p~\ddot{\sqcup}~p' \eqdef \lambda d.p(d)~\dot{\sqcup}~p'(d)$.

In Figure~\ref{def-propagators}, we give the definitions of propagators for addition, subtraction, multiplication and four division constraints over infinite integer intervals.
Addition and subtraction propagators are the best propagators \autorocq{}, but it is a well-known fact~\cite{cousot2021principles}.
We propose a new propagator $\isem{*}{x = y \cdot z}$ for multiplication defined using the propagators for floor and ceiling division.
We prove its soundness, best on assignment, reductivity and monotonicity properties~\autorocq{}.
The multiplication propagator is an example of function where the composition of best propagators does not preserve the best property.
Another propagator for multiplication was proposed in~\cite{apt-analysis-2007} and proven sound; we give its definition in appendix.
Our propagator is strictly stronger than the one of Apt et al.~\autorocq{}.
Experimentally, on all combinations of subintervals of $[-20,20]$ for $x,y,z$, our propagator is the best in $92.48\%$ of the cases, while the propagator of Apt et al. is the best in $90.37\%$ of the cases.
We believe there is still room for improvements, and our autoformalization approach will facilitate the verification of novel propagators for multiplication which are stronger and/or more efficient.

The main result of this paper is the definition of the best propagators for division constraints.
We first evaluate five existing constraint solvers and systems: Gecode v6.2.0~\cite{gecode}, Choco v5.0.0~\cite{choco-2022}, SWI-Prolog v10.0.0~\cite{wielemaker-swi-prolog-2012}, Eclipse v7.1~\cite{schimpf-eclipse-2012} and the Apron library v0.9.15~\cite{jeannet-apron-2009}.
We use the propagators for division in both Gecode and Choco, the symbols \texttt{//} and \texttt{div} in SWI-Prolog, and \texttt{/} in Eclipse.
Apron is not a constraint solver per-se, but an abstract interpretation library implementing, in particular, the interval abstract domain.
It proposes a forward and backward operations which are, to the best of our knowledge, the only ones formally defined for integer division~\cite{mine-tutorial-2017}.
We always compute the fixpoint of the propagators provided by those systems.
In addition, we implemented propagators enforcing bounds($\mathbb{R}$) consistency~\cite{hull-box-consistency-1999}, denoted by $\isem{\mathbb{R}}{.}$.
Table~\ref{table-compare-overall} gives an overview of the comparisons across systems for all four divisions.
It is clear that the division propagators tested are far from being the best possible ones.

All four division propagators are defined on top of the propagator for the constraint $x = \textnormal{fdiv}^+(y,z)$ which enforces $x = \textnormal{fdiv}(y,z) \land z > 0$.
Proving properties on these propagators is a daunting task due to the high number of possible cases.
We previously managed to prove soundness by case splitting without autoformalization, however proving $\alpha$-completeness (necessary to prove the best property) turned out to be more tedious because it is not preserved under functional composition.
Nonetheless, we could reduce the number of cases by showing $\alpha$-completeness is preserved by join.
\begin{theorem}[Join preserves $\alpha$-completeness\autorocq{}]
Let $C$ and $A$ be lattices equipped with a Galois connection $C \galois{\alpha}{\gamma} A$, and $p \in A \to A$ a propagator of the form $p_1\mathbin{\dot{\sqcup}}p_2$ given $p_1,p_2 \in A \to A$ with $\dot{\sqcup}$ the pointwise join on $A$.
Then, $p$ is $\alpha$-complete iff both $p_1$ and $p_2$ are $\alpha$-complete.
\label{join-preserves-completeness-theorem}
\end{theorem}
\noindent
For example, a propagator $p_1 \in \mathbf{I}$ can be defined as $p_1(d) \eqdef \tif{d(z) \leq [0, \infty]}{f}{\dot{\bot}}$ where $f$ is the function dealing with the case $z \geq 0$; similarly a propagator $p_2 \in \mathbf{I}$ can deal with the case $z \leq 0$.
Note that a function returning $\dot{\bot} \eqdef \lambda a.\bot$ is always $\alpha$-complete but never sound.
% A relevant study of the best abstract interpretations is available in~\cite{giacobazzi2025best}.
Using autoformalization, we obtained the Rocq proofs that all four propagators are the best possible ones\autorocq{}.
In appendix, we propose an equivalent definition of $\isem{}{x = \textnormal{tdiv}(y,z)}$ that do not rely on floor division and is more efficient (only 1 join instead of 3).
It is also proven to the best propagator\autorocq{}.

\begin{figure*}[t]
  \centering
  \setlength{\fboxsep}{0.12cm}
  \setlength{\fboxrule}{0.6pt}

  \fbox{%
    \parbox{%
      \dimexpr\textwidth-2\fboxsep-2\fboxrule\relax
    }{%
      \centering
      \textbf{I. Arithmetic over $\mathbb{Z}^\infty$}\\
      \begin{displaymath}
      \begin{array}{l}
      {-x} \eqdef \begin{cases}
        {-x} & \text{if }x \in \mathbb{Z} \\
        \infty & \text{if } x = {-\infty} \\
        {-\infty} & \text{if } x = \infty
        \end{cases} \qquad
      x + y \eqdef \begin{cases}
        x + y & \text{if }x \in \mathbb{Z}, y \in \mathbb{Z}\\
        x & \text{if }x \notin \mathbb{Z} \\
        y & \text{if }x \in \mathbb{Z}, y \notin \mathbb{Z} \\
      \end{cases} \qquad
      x - y \eqdef \begin{cases}
        x - y & \text{if }x \in \mathbb{Z}, y \in \mathbb{Z}\\
        x & \text{if }x \notin \mathbb{Z} \\
        -{y} & \text{if }x \in \mathbb{Z}, y \notin \mathbb{Z} \\
      \end{cases} \\[0.6cm]
      x \cdot y \eqdef \begin{cases}
        x \cdot y & \text{if } x \in \mathbb{Z}, y \in \mathbb{Z} \\
        0 & \text{if } x = 0 \lor y = 0 \\
        \tif{\mathit{sgne}(x,y)}{\infty}{-\infty} & \text{otherwise} \\% \qquad \textit{(test if signs are identical)}\\
      \end{cases} \qquad
      \floor{\frac{x}{y}} \eqdef \begin{cases}
        \floor{\frac{x}{y}} & \text{if } x \in \mathbb{Z}, y \in \mathbb{Z} \\
        \tif{x < 0}{{-1}}{0} & \text{if } y = \infty \\
        \tif{x > 0}{{-1}}{0} & \text{if } y = -\infty \\
        \tif{y > 0}{x}{{-}x} & \text{if }x \notin \mathbb{Z} \\
      \end{cases} \\[1cm]
      \mathit{sgne}(x,y) \eqdef (x < 0) \Leftrightarrow (y < 0) \quad \textit{ (test if signs are identical) } \qquad
      \ceil{\frac{x}{y}} \eqdef {-}\floor{\frac{{-x}}{y}} \\[-0.2cm]
      % \begin{cases}
      %   \mathit{cdiv}(x,y) & \text{if } x \in \mathbb{Z}, y \in \mathbb{Z} \\
      %   \tif{x > 0}{1}{0} & \text{if } x \in \mathbb{Z}, y = \infty \\
      %   \tif{x < 0}{1}{0} & \text{if } x \in \mathbb{Z}, y = -\infty \\
      %   \tif{y > 0}{x}{{\overline{-}}x} & \text{if }x \notin \mathbb{Z}  \\
      % \end{cases}  \qquad \text{ with } y \neq 0 \\
      \end{array}
      \end{displaymath}
      \begin{minipage}{0.2\textwidth}
      \begin{displaymath}
      \begin{array}{l}
      \textbf{II. Interval Arithmetic}\\[0.1cm]
      v \notin [a,b] \eqdef a > v \lor b < v \\
      \mathit{neg}([a,b]) \eqdef [-b, -a] \\
      \mathit{add}([a,b], [c,d]) \eqdef [a + c, b + d] \\
      \mathit{sub}([a,b], [c,d]) \eqdef [a - d, b - c] \\
      \mathit{mul}([a,b], [c,d]) \eqdef \\
      \quad [\mathit{min} \{a \cdot c, a \cdot d, b \cdot c, b \cdot d\},\\
      \quad \phantom{[}\mathit{max}\{a \cdot c, a \cdot d, b \cdot c, b \cdot d\}]
      \end{array}
      \end{displaymath}
      \begin{displaymath}
      \begin{array}{l}
      \textbf{III. Addition and Subtraction Propagators}\\[0.1cm]
      \isem{}{x = y + z}d = \\
      \quad d(x) \leftarrow \mathit{add}(d(y), d(z)) \\
      \quad d(y) \leftarrow \mathit{sub}(d(x), d(z)) \\
      \quad d(z) \leftarrow \mathit{sub}(d(x), d(y)) \\
      \quad \textbf{return } d\\[0.2cm]

      \isem{}{x = y - z} = \isem{}{y = x + z} \\[0.2cm]
      \end{array}
      \end{displaymath}
      \begin{displaymath}
      \begin{array}{l}
      \textbf{IV. Multiplication Propagator}\\[0.1cm]
      \isem{*}{x = y \cdot z}d \eqdef \\
      \quad d(x) \leftarrow \mathit{mul}(d(y), d(z)) \\
      \quad \textbf{if } 0 \notin d(x) \lor 0 \notin d(z) \textbf{ then}\\
      \qquad d = \isem{}{y = \textnormal{cdiv}(x,z)}d \\
      \qquad d = \isem{}{y = \textnormal{fdiv}(x,z)}d\\
      \quad \textbf{if } 0 \notin d(x) \lor 0 \notin d(y) \textbf{ then}\\
      \qquad d = \isem{}{z = \textnormal{cdiv}(x,y)}d \\
      \qquad d = \isem{}{z = \textnormal{fdiv}(x,y)}d \\
      \quad \textbf{return } d \\[0.2cm]
      \end{array}
      \end{displaymath}
      \end{minipage}%
      \hfill
      \begin{minipage}{0.53\textwidth}
      \begin{displaymath}
      \begin{array}{l}
      \textbf{V. Floor Division Propagator (z > 0)}\\[0.1cm]
      \textbf{precondition: } zl \neq 0 \land zu \neq 0\\
      \mathit{fdiv}^{+}([yl,yu], [zl,zu]) \eqdef\\
      \quad [\mathit{min} \{\floor{\frac{yl}{zl}}, \floor{\frac{yl}{zu}}, \floor{\frac{yu}{zl}}, \floor{\frac{yu}{zu}}\}, \phantom{[}\mathit{max} \{\floor{\frac{yl}{zl}}, \floor{\frac{yl}{zu}}, \floor{\frac{yu}{zl}}, \floor{\frac{yu}{zu}}\}] \\[0.5cm]

      \mathit{fden}^{+}([xl,xu],[yl,yu]) \eqdef \\
      \quad z = [1, \infty] \\
      % \quad \textit{(Enforce } xl \cdot z \leq yu \textit{)} \\
      \quad \textbf{if } xl > 0 \textbf{ then } z \leftarrow [-\infty, \floor{\frac{yu}{xl}}] \\[0.1cm]
      \quad \textbf{else if } xl \neq 0 \textbf{ then } z \leftarrow [\ceil{\frac{yu}{xl}}, \infty] \\[0.1cm]
      \quad \textbf{else if } yu < 0 \textbf{ then } \textbf{return } \bot \\
      % \quad \textit{(Enforce } (xu + 1) \cdot z \geq yl + 1 \textit{)} \\
      \quad \textbf{if } xu > {-1} \textbf{ then } z \leftarrow [\ceil{\frac{yl + 1}{xu + 1}}, \infty] \\
      \quad \textbf{else if } xu \neq {-1} \textbf{ then } z \leftarrow [-\infty, \floor{\frac{yl+1}{xu + 1}}] \\
      \quad \textbf{else if } yl \geq 0 \textbf{ then } \textbf{return } \bot \\
      \quad \textbf{return } z\\[0.3cm]

      % \textit{(hull of }[xl \cdot  z , (xu+1) \cdot z - 1]\textit{)}\\
      \mathit{fnum}^{+}([xl,xu],[zl,zu]) \eqdef \\
      \quad \textbf{return } [\mathit{min} \{xl \cdot zl, xl \cdot zu\},\\
      \quad \phantom{\textbf{return } [}\mathit{max}\{(xu + 1) \cdot zl - 1, (xu + 1) \cdot zu - 1\}]\\[0.3cm]

      % \textit{Enforce } x = \textnormal{fdiv}(y,z) \land z \geq 1 \\
      \isem{}{x = \textnormal{fdiv}^{+}(y, z)}d = \\
      \quad d(z) \leftarrow \mathit{fden}^{+}(d(x), d(y)) \\
      \quad d(y) \leftarrow \mathit{fnum}^{+}(d(x), d(z)) \\
      \quad d(x) \leftarrow \mathit{fdiv}^{+}(d(y), d(z)) \\
      \quad \textbf{return } d\\[0.3cm]

      \mathit{zneg}_{xy}(d) \eqdef d[x \mapsto \mathit{neg}(d(x)), y \mapsto \mathit{neg}(d(y))]\\
      \mathit{pos}_x(d) \eqdef d[x \mapsto d(x) \sqcap [0, \infty]] \\
      \mathit{neg}_x(d) \eqdef d[x \mapsto d(x) \sqcap [-\infty, 0]] \\[0.3cm]
      \end{array}
      \end{displaymath}
      \end{minipage}\\
      \textbf{VI. Integer Division Propagators}
      \begin{displaymath}
      \begin{array}{l}
      \isem{}{x = \textnormal{fdiv}(y, z)} = \isem{}{x = \textnormal{fdiv}^{+}(y, z)} \mathbin{\ddot{\sqcup}} (\mathit{zneg}_{yz} \circ \isem{}{x = \textnormal{fdiv}^{+}(y, z)} \circ \mathit{zneg}_{yz})\\
      \isem{}{x = \textnormal{cdiv}(y, z)} = (\mathit{zneg}_{xy} \circ \isem{}{x = \textnormal{fdiv}^{+}(y, z)} \circ \mathit{zneg}_{xy}) \mathbin{\ddot{\sqcup}} (\mathit{zneg}_{xz} \circ \isem{}{x = \textnormal{fdiv}^{+}(y, z)} \circ \mathit{zneg}_{xz})\\
      \isem{}{x = \textnormal{ediv}(y, z)} = \isem{}{x = \textnormal{fdiv}^{+}(y, z)} \mathbin{\ddot{\sqcup}} (\mathit{zneg}_{xz} \circ \isem{}{x = \textnormal{fdiv}^{+}(y, z)} \circ \mathit{zneg}_{xz})\\
      \isem{}{x = \textnormal{tdiv}(y, z)} = \\
        \quad \phantom{\mathbin{\ddot{\sqcup}}\; \mathit{zneg}_{xz} \circ }\;\; (\isem{}{x = \textnormal{fdiv}^{+}(y, z)} \circ \mathit{pos}_y) \hfill \textit{(quadrant 1: } y=[0,\infty], z=[1,\infty]\textit{)} \\
        \quad \mathbin{\ddot{\sqcup}}\; (\mathit{zneg}_{xz} \circ \isem{}{x = \textnormal{fdiv}^{+}(y, z)} \circ \mathit{zneg}_{xz} \circ \mathit{pos}_y) \hfill \textit{(quadrant 2: } y=[0,\infty], z=[-\infty, -1]\textit{)}\\
        \quad \mathbin{\ddot{\sqcup}}\; (\mathit{zneg}_{xy} \circ \isem{}{x = \textnormal{fdiv}^{+}(y, z)} \circ \mathit{zneg}_{xy} \circ \mathit{neg}_y) \hfill \textit{(quadrant 3: } y=[-\infty, 0], z=[1, \infty]\textit{)}\\
        \quad \mathbin{\ddot{\sqcup}}\; (\mathit{zneg}_{yz} \circ \isem{}{x = \textnormal{fdiv}^{+}(y, z)} \circ \mathit{zneg}_{yz} \circ \mathit{neg}_y) \hfill \textit{(quadrant 4: } y=[-\infty, 0], z=[-\infty, -1]\textit{)}
      \end{array}
      \end{displaymath}
    }
  }

  \caption{Definition of interval propagators.}
  \label{def-propagators}
\end{figure*}

\section{Appendix}


\begin{figure*}[t]
  \centering
  \setlength{\fboxsep}{0.2cm}
  \setlength{\fboxrule}{0.6pt}

  \fbox{%
    \parbox{%
      \dimexpr\textwidth-2\fboxsep-2\fboxrule\relax
    }{%
      \centering
      \begin{displaymath}
      \begin{array}{l}
      \textbf{precondition: } zl \neq 0 \land zu \neq 0\\
      \mathit{tdiv}^{+}([yl,yu], [zl,zu]) \eqdef [\mathit{min} \{[\frac{yl}{zl}], [\frac{yl}{zu}], [\frac{yu}{zl}], [\frac{yu}{zu}]\}, \mathit{max} \{[\frac{yl}{zl}], [\frac{yl}{zu}], [\frac{yu}{zl}], [\frac{yu}{zu}]\}] \\[0.5cm]

      \mathit{tden}^{+}([xl,xu],[yl,yu]) \eqdef \\
      \quad z = [1, \infty] \\
      \quad \textbf{if } xl > 0 \textbf{ then } z \leftarrow [-\infty, \floor{\frac{yu}{xl}}] \\[0.1cm]
      \quad \textbf{else } z \leftarrow [\ceil{\frac{yu - 1}{xl - 1}}, \infty] \\
      \quad \textbf{if } xu > {-1} \textbf{ then } z \leftarrow [\ceil{\frac{yl + 1}{xu + 1}}, \infty] \\
      \quad \textbf{else } z \leftarrow [-\infty, \floor{\frac{yl}{xu}}] \\
      \quad \textbf{return } z\\[0.3cm]

      \mathit{tnum}^{+}([xl,xu],[zl,zu]) \eqdef \\
      \quad \textbf{return } [\tif{xl > 0\;}{\mathit{min} \{ xl \cdot zl, xl \cdot zu \}\;\;}{\mathit{min} \{((xl - 1) \cdot zl) + 1, ((xl - 1) \cdot zu) + 1\}}, \\
      \quad \phantom{ \textbf{return } [}\tif{xu < 0}{\mathit{max} \{xu \cdot zl, xu \cdot zu\}}{\mathit{max} \{ ((xu + 1) \cdot zl) - 1, ((xu + 1) \cdot zu) - 1 \}}] \\[0.3cm]

      % \textit{Enforce } x = \textnormal{tdiv}(y,z) \land z \geq 1 \\
      \isem{}{x = \textnormal{tdiv}^{+}(y, z)}d \eqdef \\
      \quad d(z) \leftarrow \mathit{tden}^{+}(d(x), d(y)) \\
      \quad d(y) \leftarrow \mathit{tnum}^{+}(d(x), d(z)) \\
      \quad d(x) \leftarrow \mathit{tdiv}^{+}(d(y), d(z)) \\
      \quad \textbf{return } d\\[0.3cm]

      \isem{}{x = \textnormal{tdiv}(y, z)} \eqdef \isem{}{x = \textnormal{tdiv}^{+}(y, z)} \mathbin{\ddot{\sqcup}} (\mathit{zneg}_{xz} \circ \isem{}{x = \textnormal{tdiv}^{+}(y, z)} \circ \mathit{zneg}_{xz})\\
      \end{array}
      \end{displaymath}
    }
  }
  \caption{Simplified truncated division.}
  \label{simplified-tdiv}
\end{figure*}


\begin{figure*}[t]
  \centering
  \setlength{\fboxsep}{0.2cm}
  \setlength{\fboxrule}{0.6pt}

  \fbox{%
    \parbox{%
      \dimexpr\textwidth-2\fboxsep-2\fboxrule\relax
    }{%
      \centering
      \begin{displaymath}
      \begin{array}{l}
      \textbf{Interval Arithmetic}\\[0.1cm]
      \mathit{neqzero}([a,b]) \eqdef [\tif{a=0}{1}{a}, \tif{b=0}{{-1}}{b}] \\
      \mathit{mul}([a,b], [c,d]) \eqdef \\
      \quad [\mathit{min} \{a \cdot c, a \cdot d, b \cdot c, b \cdot d\},\\
      \quad \phantom{[}\mathit{max}\{a \cdot c, a \cdot d, b \cdot c, b \cdot d\}]\\[0.2cm]

      \textbf{Multiplication Propagator}\\[0.1cm]
      \isem{**}{x = y \cdot z}d \eqdef \\
      \quad d(x) \leftarrow \mathit{mul}(d(y), d(z)) \\
      \quad \textbf{if } 0 \notin d(x) \textbf{ then } d(z) \leftarrow \mathit{neqzero}(d(z)) \\
      \quad d(y) \leftarrow \mathit{mulback}(d(x), d(z)) \\
      \quad \textbf{if } 0 \notin d(x) \textbf{ then } d(y) \leftarrow \mathit{neqzero}(d(y)) \\
      \quad d(z) \leftarrow \mathit{mulback}(d(x), d(y)) \\
      \quad \textbf{return } d\\[0.2cm]

      \mathit{mulback}([a,b],[c,d]) \eqdef \\
      \quad \textbf{if } c > 0 \lor d < 0 \textbf{ then }\\
      \qquad [\mathit{min}\{\ceil{\frac{a}{c}}, \ceil{\frac{a}{d}}, \ceil{\frac{b}{c}}, \ceil{\frac{b}{d}}\}, \mathit{max} \{\floor{\frac{a}{c}}, \floor{\frac{a}{d}}, \floor{\frac{b}{c}}, \floor{\frac{b}{d}}\}] \\[0.1cm]
      \quad \textbf{else if } c < 0 \land d > 0 \land (a > 0 \lor b < 0) \textbf{ then } [\mathit{min}(a,-b), \mathit{max}(-a, b)] \\
      \quad \textbf{else } \top \\[0.2cm]
      \end{array}
      \end{displaymath}
    }
  }

  \caption{Two propagators for multiplication constraint. $\isem{**}{x = y \cdot z}$ implements the propagator in~\cite{apt-analysis-2007}.}
  \label{apt-multiplication-prop}
\end{figure*}

\end{document}

For every occurrence of the command \autorocq in the paper above, give a proof of the claim in a Rocq file claimX.v where X in the number of the claim. You can Require other claimX.v and add the claims to _CoqProject. Do not copy paste previous definitions if it is not necessary. Use Rocq-MCP. Proceed carefully for each claim, it is going to be a long work. Do not leave any Assume. Prove everything. Don't check by brute-force the correctness of the propagators, they are correct, proceed directly with the proof.