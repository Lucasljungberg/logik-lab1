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
    iterate(Prems, Tail, Proof), !.

box_iterator([], _) :- !.
box_iterator([BoxHead | BoxTail], Proof) :-
	check_proof(_, BoxHead, Proof),
	box_iterator(BoxTail, [Proof | BoxHead]), !.
    
append_list([],List,List).                            
append_list([Head | FirstTail], List2, [Head|NewTail]) :- append(FirstTail,List2,NewTail).

find_nth(N, [Head | _], Row) :-
	nth0(0, Head, Nr),
	N = Nr,
	Head = Row, !.
find_nth(N, [ [ [Nr, Action, assumption] | BoxTail ] | Tail ], Row) :-
    append_list([ [ Nr, Action, assumption] | BoxTail], Tail, NewList),
	find_nth(N, NewList, Row), !.
find_nth(N, [_| Tail], Row):-
	find_nth(N, Tail, Row), !.
find_nth(_, [], _).

is_in_scope(Row, [Head | _]) :-
    nth0(0, Head, Nr),
    Row = Nr, !.
is_in_scope(Row, [ _ | Tail]) :-
    is_in_scope(Row, Tail), !.
is_in_scope(_, []).

%% Extracts the proof from the given lines
check_lines(_, Line1, Line2, _, Proof, Action1, Action2) :-
    is_in_scope(Line1, Proof),
    is_in_scope(Line2, Proof),
    find_nth(Line1, Proof, Proof1),  %% Loads the proofrows from the specified lines
    find_nth(Line2, Proof, Proof2),
    nth0(1, Proof1, Action1),   %% Loads the action from each line
    nth0(1, Proof2, Action2).
    
check_lines(_, Line, _, Proof, Action) :-
    find_nth(Line, Proof, ProofRow),
    nth0(1, ProofRow, Action).

%% Checks if the last line of proof matches with goal 
check_goal(Goal, Proof) :-
    last(Proof, ProofLine),         %% Gets the last line of proof.
    nth0(1, ProofLine, GoalMatch),  %% Extracts the middle part of the line.
    GoalMatch = Goal.               %% Checks if Goal matches the last line of proof.    

%% Base case
check_proof(_, [], _) :- !.

%% Matches for premise and checks if it is indeed a premise
check_proof(Prems, [_, Action, premise], _) :-
    member(Action, Prems), !.

%% Matches for conjunction
check_proof(_, [Nr, and(X,Y), Rule], Proof) :-
    check_rule(Nr, and(X,Y), Rule, Proof), !. 

%% Finds match for imp rule as action
check_proof(_, [Nr, imp(X,Y), Rule], Proof) :-
    check_rule(Nr, imp(X,Y), Rule, Proof), !.

check_proof(_, [[_, _, assumption] | Tail], Proof) :-
    box_iterator(Tail, Proof).

%% Matches for single-element actions
check_proof(_, [Nr, X, Rule], Proof) :-
    check_rule(Nr, X, Rule, Proof), !.
    
%% Checks that implication elimination is done correctly
check_rule(Nr, Action, impel(X,Y), Proof) :-
    (Nr > X), (Nr > Y),
    check_lines(Action, X, Y, impel(X,Y), Proof, Action1, Action2),
    imp(Action1, Action) = Action2, !. 
    
check_rule(Nr, Action, impint(X,Y), Proof) :-
    (Nr > X), (Nr > Y),
    check_lines(Action, X, Y, impint(X,Y), Proof, Copy1, Copy2),
    imp(Copy1, Copy2) = Action.

%% Checks that and elimination is done correctly (May need tweek)
check_rule(Nr, Action, andel(X,Y), Proof) :-
    (Nr > X), (Nr > Y),
    check_lines(Action, X, Y, andel(X,Y), Proof, Action1, Action2),
    (and(Action1, Action2) = Action ; and(Action2, Action1) = Action)
    ,!.
    
check_rule(Nr, Action, copy(X), Proof) :-
    (Nr > X),
    check_lines(_, X, _, Proof, Copied),
    Action = Copied. 
    
check_rule(Nr, Action, andint(X, Y), Proof) :-
    Nr > X, (Nr > Y),
    check_lines(Action, X, Y, andint(X,Y), Proof, Copy1, Copy2),
    (Action = and(Copy1, Copy2) ; Action = and(Copy2, Copy1)).

check_rule(Nr, Action, andel1(X), Proof) :-
    (Nr > X),
    check_lines(Action, X, andel1(X), Proof, Copied), 
    (Copied = and(Action,_)).

check_rule(Nr, Action, andel2(X), Proof) :-
    (Nr > X),
    check_lines(Action, X, andel1(X), Proof, Copied),
    (Copied = and(_,Action)).

check_rule(Nr, Action, negel(X, Y), Proof) :-
    (Nr > X), (Nr > Y),
    check_lines(Action, X, Y, negel(X,Y), Proof, Copy1, Copy2),
    ((Copy1 = neg(_A), Copy2 = _B) ; (Copy1 = _A, Copy2 = neg(_B))).

check_rule(Nr, Action, contel(X), Proof) :-
    (Nr > X),
    check_lines(Action, X, contel(X), Proof, Copied),
    Copied = cont, !.
    
check_rule(Nr, Action, negnegint(X), Proof) :-
    (Nr > X),
    check_lines(Action, X, negnegint(X), Proof, Copied),
    Action = neg(neg(Copied)).
    
check_rule(Nr, Action, negnegel(X), Proof) :-
    (Nr > X),
    check_lines(Action, X, negnegel(X), Proof, Copied),
    neg(neg(Action)) = Copied.
    
check_rule(Nr, Action, mt(X, Y), Proof) :-
    (Nr > X), (Nr > Y),
    check_lines(Action, X, Y, mt(X,Y), Proof, Copy1, Copy2),
    Action = neg(_a),
    Copy2 = neg(_b),
    Copy1 = imp(_a, _b), 
    !.
check_rule(Nr, Action, orint1(X), Proof) :-
    not(Nr > X),
    check_lines(Action, X, orint1(X), Proof, Copied),
    (Copied = or(Action, _) ; Copied = or(_, Action)), !.

check_rule(Nr, Action, orint2(X), Proof) :-
    (Nr > X),
    check_lines(Action, X, orint2(X), Proof, Copied),
    (Copied = or(Action, _) ; Copied = or(_, Action)), !.

check_rule(Nr, _, orel(R, X, Y, A, B), Proof) :-
    find_nth(R, Proof, First),
    find_nth(X, Proof, First1),
    find_nth(Y, Proof, Last1),
    find_nth(A, Proof, First2),
    find_nth(B, Proof, Last2),
    nth0(1, First, Prev),
    nth0(1, First1, Assumption1),
    nth0(1, First2, Assumption2),
    nth0(1, Last1, Goal1),
    nth0(1, Last2, Goal2),
    Goal1 = Goal2,
    (or(Assumption1, Assumption2) = Prev ; or(Assumption2, Assumption1) = Prev),
    !.

check_rule(Nr, Action, negint(X,Y), Proof) :-
    (Nr > X), (Nr > Y),
    find_nth(X, Proof, First),
    find_nth(Y, Proof, Last),
    nth0(1, First, Before), 
    nth0(1, Last, Cont),
    Cont = cont,
    neg(Before) = Action.    

check_rule(Nr, Action, lem, _) :-
    Action = or(X, neg(X)).

check_rule(Nr, Action, pbc(X, Y), Proof) :-
    find_nth(X, Proof, First),
    find_nth(Y, Proof, Last),
    nth0(1, First, Before), 
    nth0(1, Last, Cont),
    Cont = cont,
    Before = neg(Action).  

    
    
    
    
    
    
