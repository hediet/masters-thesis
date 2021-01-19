
* Introduction - *Sehr knappe Beschreibung von LYG + Motivation warum formaler Beweis interessant* (1p)
* Background {14p} - *Idee: Wenn man die Themen hier gut kennt, kann man die Kapitel problemlos überspringen. Nix neues hier.*
    * Lower Your Guards [9p]
        * Motivation - *Welches Problem loest LYG? (Beispiele!)* (2p)
        * Strictness - *Anhand eines Haskell-Beispiel Strictness-Fallstricke erläutern* (1p)
        * Guard Trees - *Problem-Reduktion erklären. Nicht auf Funktion `𝒟` eingehen.* (1p)
        * Refinement Types - *Erklären + Funktion G postulieren* (1p)
        * Uncovered Analysis - *𝒰 erklären* (1p)
        * Redundant/Inaccessible Analysis - *ℛ erklären* (1p)
    * Lean [4p]
        * Lean Prover - *Übersicht zum Lean-Prover* (3p)
        * Mathlib - *Übersicht über finset, list, multiset* (1p)
* Formalization {13p}
    * Formalization Gap - *Welche Probleme gab es beim Formalisieren des Papers? (`and`)* (2p)
    * Definitions - *Walkthrough durch alle Definitionen aus definitions.lean. Tradeoffs diskutieren. Vielleicht Unterkapitel zu den einzelnen Definitionen anlegen.* (6p)
    * Correctness-Statements - *Walkthrough durch theorems.lean (ohne die Beweise)* (4p)
* Formalized Proof {17p}
    * Overview - *Übersicht des Beweises ohne Lean Code anhand von Diagrammen* (3p)
    * Definitions of U, A, R, Ant implies - *Motivation dieser internen Definitionen erklären* (4p)
    * R is not monotonous - *Problematisch für Beweis-Abstraktion. Hinleitung auf `is_redundant_set`* (2p)
    * Definition of `is_redundant_set` (1p)
    * Main Proof - *Detailierter Walkthrough durch Lean Code von `R_red_removable`. Einziger Beweis-Abdruck.* (4p)
    * Alternative Proof Ideas *Auf direkten induktiven Beweis eingehen. Kurze Diskussion um Eleminierung von Bang* (1p)
* Conclusion {1p} - *Erwähnung der Formalization Gap. Ja, LYG ist korrekt! Komplexität des Beweises diskutieren* (1p)

~45 Seiten
+ 5 Inhaltsverzeichnis etc.
+ 3 Am Ende
= Total 53 Seiten
