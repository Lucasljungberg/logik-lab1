% Lab 1 in Logic in Computer Science course
% Authors:
%           Lucas Ljungberg <lucaslj@kth.se>
%           Anton Ronsjö    <ronsjo@kth.se>
%

%% Startpoint of the program.
verify(InputFileName) :-
    see(InputFileName), read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Goal, Proof),
    iterate(Prems, Proof, Proof).

%% Checks if goal is valid
valid_proof(Goal, Proof) :-
    check_goal(Goal, Proof)
    .

%% Iterates through the proof-list
iterate(_, [], _) :- !.
iterate(Prems, [Head | Tail], Proof) :-
    check_proof(Prems, Head, Proof),
    iterate(Prems, Tail, Proof).
    
box_iterator(StartRow, Box) :-
    
    

%% Extracts the proof from the given lines
check_lines(_, Line1, Line2, _, Proof, Action1, Action2) :-
    Row1 is Line1 - 1,
    Row2 is Line2 - 1,
    nth0(Row1, Proof, Proof1),  %% Loads the proofrows from the specified lines
    nth0(Row2, Proof, Proof2),
    nth0(1, Proof1, Action1),   %% Loads the action from each line
    nth0(1, Proof2, Action2).
    
check_lines(_, Line, _, Proof, Action) :-
    Row is Line - 1,
    nth0(Row, Proof, ProofRow),
    nth0(1, ProofRow, Action).
    

%% Checks if the last line of proof matches with goal 
check_goal(Goal, Proof) :-
    last(Proof, ProofLine),         %% Gets the last line of proof.
    nth0(1, ProofLine, GoalMatch),  %% Extracts the middle part of the line.
    Goal = GoalMatch.               %% Checks if Goal matches the last line of proof.    


%% Base case
check_proof(_, [], _) :- !.

%% Matches for premise and checks if it is indeed a premise
check_proof(Prems, [_, Action, premise], _) :-
    member(Action, Prems), !.

%% Matches for conjunction
check_proof(_, [_, and(X,Y), Rule], Proof) :-
    check_rule(and(X,Y), Rule, Proof), !. 

%% Finds match for imp rule as action
check_proof(_, [_, imp(X,Y), Rule], Proof) :-
    check_rule(imp(X,Y), Rule, Proof), !.

check_proof(Prems, [[Nr, Assumption, assumption] | Tail], Proof) :-
    writeln(Assumption),
    iterate(Prems, Tail, Tail).

%% Matches for single-element actions
check_proof(_, [_, X, Rule], Proof) :-
    check_rule(X, Rule, Proof), !.
    
%% Checks that implication elimination is done correctly
check_rule(Action, impel(X,Y), Proof) :-
    check_lines(Action, X, Y, impel(X,Y), Proof, Action1, Action2),
    imp(Action1, Action) = Action2, !. 
    
check_rule(Action, impint(X,Y), Proof) :-
    check_lines(Action, X, Y, impint(X,Y), Copy1, Copy2),
    imp(Copy1, Copy2) = Action.

%% Checks that and elimination is done correctly (May need tweek)
check_rule(Action, andel(X,Y), Proof) :-
    check_lines(Action, X, Y, andel(X,Y), Proof, Action1, Action2),
    (and(Action1, Action2) = Action ; and(Action2, Action1) = Action)
    ,!.
    
check_rule(Action, copy(X), Proof) :-
    check_lines(Action, X, copy(X), Proof, Copied),
    Action = Copied. 
    
check_rule(Action, andint(X, Y), Proof) :-
    check_lines(Action, X, Y, andint(X,Y), Proof, Copy1, Copy2),
    (Action = and(Copy1, Copy2) ; Action = and(Copy2, Copy1)).

check_rule(Action, andel1(X), Proof) :-
    check_lines(Action, X, andel1(X), Proof, Copied),
    (Copied = and(X, Y) ; Copied = and(Y,X)).

check_rule(Action, andel2(X), Proof) :-
    check_lines(Action, X, andel1(X), Proof, Copied),
    (Copied = and(X, Y) ; Copied = and(Y,X)).

check_rule(Action, negel(X, Y), Proof) :-
    check_lines(Action, X, Y, negel(X,Y), Proof, Copy1, Copy2),
    (Copy1 = neg(A), Copy2 = B) ; (Copy1 = A, Copy2 = neg(B)).

check_rule(Action, contel(X), Proof) :-
    check_lines(Action, X, contel(X), Proof, Copied),
    Copied = cont.
    
check_rule(Action, negnegint(X), Proof) :-
    check_lines(Action, X, negnegint(X), Proof, Copied),
    Action = negneg(Copied).
    
check_rule(Action, negnegel(X), Proof) :-
    check_lines(Action, X, negnegel(X), Proof, Copied),
    negneg(Action) = Copied.
    
check_rule(Action, mt(X, Y), Proof) :-
    check_lines(Action, X, Y, mt(X,Y), Proof, Copy1, Copy2),
    Copy1 = imp(neg(Copy2), neg(Action)),
    Copy2 = neg(A),
    Action = neg(B).

    
    
    

    
    
    
    
    
    
    
    
    
    
    
