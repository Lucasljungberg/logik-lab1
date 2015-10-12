% Lab 1 in Logic in Computer Science course
% Authors:
%           Lucas Ljungberg <lucaslj@kth.se>
%           Anton Ronsjö    <ronsjo@kth.se>
%


verify(InputFileName) :-
    see(InputFileName), read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Goal, Proof),
    iterate(Prems, Proof).

valid_proof(Goal, Proof) :-
    check_goal(Goal, Proof)
    .

iterate(_, []) :- !.
iterate(Prems, [Head | Tail]) :-
    check_proof(Prems, Head, Proof),
    iterate(Prems, Tail).
    

check_lines(Action, Line1, Line2, Rule, Proof) :-
    Row1 is Line1 - 1,
    Row2 is Line2 - 1,
    nth0(Row1, Proof, Proof1),  %% Loads the proofrows from the specified lines
    nth0(Row2, Proof, Proof2),
    nth0(1, Proof1, Action1),   %% Loads the action from each line
    nth0(1, Proof2, Action2),
    member(Action1, Action2).
    

%% Checks if the last line of proof matches with goal 
check_goal(Goal, Proof) :-
    last(Proof, ProofLine),         %% Gets the last line of proof.
    nth0(1, ProofLine, GoalMatch),  %% Extracts the middle part of the line.
    Goal = GoalMatch.               %% Checks if Goal matches the last line of proof.    


check_proof(_, [], _) :- !.

check_proof(Prems, [Nr, Action, premise], Proof) :-
    member(Action, Prems), !.

%% Finds match for imp rule as action
check_proof(_, [Nr, imp(X,Y), Rule], Proof) :-
    check_rule(imp(X,Y), Rule, Proof), !. 
    
check_proof(_, [Nr, X, Rule], Proof) :-
    check_rule(X, Rule, Proof), !.
    
check_rule(Action, impel(X,Y), Proof) :-
    check_lines(Action, X, Y, impel(X,Y), Proof), !. 
    
    
    
    
    
    
    
    
    