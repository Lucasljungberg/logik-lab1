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
    

%% Extracts the proof from the given lines
check_lines(_, Line1, Line2, _, Proof, Action1, Action2) :-
    Row1 is Line1 - 1,
    Row2 is Line2 - 1,
    nth0(Row1, Proof, Proof1),  %% Loads the proofrows from the specified lines
    nth0(Row2, Proof, Proof2),
    nth0(1, Proof1, Action1),   %% Loads the action from each line
    nth0(1, Proof2, Action2).
    

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

%% Matches for disjunction
check_proof(_, [_, or(X,Y), Rule], Proof) :-
    check_rule(or(X,Y), Rule, Proof)
    ,!. 

%% Matches for single-element actions
check_proof(_, [_, X, Rule], Proof) :-
    check_rule(X, Rule, Proof), !.
    
%% Checks that implication elimination is done correctly
check_rule(Action, impel(X,Y), Proof) :-
    check_lines(Action, X, Y, impel(X,Y), Proof, Action1, Action2),
    imp(Action1, Action) = Action2, !. 

%% Checks that and elimination is done correctly (May need tweek)
check_rule(Action, andel(X,Y), Proof) :-
    check_lines(Action, X, Y, andel(X,Y), Proof, Action1, Action2),
    (and(Action1, Action2) = Action ; and(Action2, Action1) = Action)
    ,!.

check_rule(Action, orel(X,Y), Proof) :-
    check_lines(Action, X, Y, orel(X,Y), Proof, Action1, Action2),
    (or(Action1, Action2) = Action ; and(Action2, Action1) = Action),
    !.


    
    
    
    
    
    
    
    
    
