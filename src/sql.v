Require Import List.

Require Import String.
Require Import Strings.String.
Open Scope string_scope.

(* for pretty printing nats as strings *)
Require Import Numbers.DecimalNat.
Require Import Numbers.DecimalString.

Definition sqlIdentifier := string.
Inductive sqlColumnType := sqlStringType | sqlIntType | sqlUnknownType.
Inductive sqlDecl :=
    | sqlTableDecl: sqlIdentifier -> list (string * sqlColumnType) -> sqlDecl
    | sqlInsert: sqlIdentifier -> list string -> sqlDecl.

Inductive sqlLiteral :=
    | sqlNaturalNumber: nat -> sqlLiteral
    | sqlTrue
    | sqlFalse.

Inductive sqlScalarExpression :=
    | sqlExprFromLiteral: sqlLiteral -> sqlScalarExpression
    | sqlEq: sqlScalarExpression -> sqlScalarExpression -> sqlScalarExpression
    | sqlAnd: sqlScalarExpression -> sqlScalarExpression -> sqlScalarExpression
    | sqlColumnValue: sqlIdentifier -> sqlScalarExpression.

Inductive sqlQuery :=
    | sqlSelect: sqlColumnExpression -> sqlTableExpression -> sqlScalarExpression -> sqlQuery
    | sqlUnion: sqlQuery -> sqlQuery -> sqlQuery
    | sqlIntersect: sqlQuery -> sqlQuery -> sqlQuery
    | sqlExcept: sqlQuery -> sqlQuery -> sqlQuery

  with sqlTableExpression :=
    | sqlTable: sqlIdentifier -> sqlTableExpression
    | sqlCrossProduct: sqlTableExpression -> sqlTableExpression -> sqlTableExpression
    | sqlTableFromQuery: sqlQuery -> sqlTableExpression

  with sqlColumnExpression :=
    | sqlAllColumns
    | sqlDistinct: sqlColumnExpression -> sqlColumnExpression
    | sqlColumnList: list sqlIdentifier -> sqlColumnExpression.

Coercion sqlTableFromQuery : sqlQuery >-> sqlTableExpression.

Definition stringToColumnValue := fun (s: string) => sqlColumnValue s.
Coercion stringToColumnValue : string >-> sqlScalarExpression.
Coercion sqlExprFromLiteral: sqlLiteral >-> sqlScalarExpression.
Definition stringToTable := fun (s: string) => sqlTable s.
Coercion stringToTable : string >-> sqlTableExpression.

Definition sqlProj := fun c => fun t => sqlSelect c t sqlTrue.

Definition sqlSignature := list sqlDecl.
Definition sqlTheory := list sqlQuery.
Definition sqlSystem := (sqlSignature * sqlTheory)%type.

Definition sqlPrettyPrintType (tp: sqlColumnType): string := match tp with
| sqlStringType => "VARCHAR(200)"
| sqlIntType => "INT"
| sqlUnknownType => "???UNKNOWN-TYPE???"
end.

Definition sqlPrettyPrintDecl (decl: sqlDecl): string := match decl with
| sqlTableDecl t c => let columnStr := concat ", " (map (fun col => match col with | (name, tp) => "`" ++ name ++ "` " ++ sqlPrettyPrintType tp end) c) in
    "CREATE TABLE `" ++ t ++ "` (" ++ columnStr ++ ")"
| sqlInsert t v => "INSERT INTO `" ++ t ++ "` (" ++ (concat ", " v) ++ ")"
end.

Fixpoint sqlPrettyPrintScalarExpr (s: sqlScalarExpression): string := match s with
| sqlExprFromLiteral l => match l with
  | sqlNaturalNumber n => (NilZero.string_of_uint (Unsigned.to_lu n))
  | sqlTrue => "true"
  | sqlFalse => "false"
  end
| sqlEq e1 e2 => "(" ++ sqlPrettyPrintScalarExpr e1 ++ ") = (" ++ sqlPrettyPrintScalarExpr e2 ++ ")"
| sqlAnd e1 e2 => "(" ++ sqlPrettyPrintScalarExpr e1 ++ ") AND (" ++ sqlPrettyPrintScalarExpr e2 ++ ")"
| sqlColumnValue id => "`" ++ id ++ "`"
end.

Fixpoint sqlPrettyPrintQuery (q: sqlQuery): string := match q with
| sqlSelect c t p =>
       "SELECT * FROM ("
    ++ sqlPrettyPrintTableExpr t
    ++ ")"
    ++ match p with
    | sqlTrue => ""
    | _ => " WHERE " ++ sqlPrettyPrintScalarExpr p
    end
| sqlUnion q1 q2 => "(" ++ sqlPrettyPrintQuery q1 ++ ") UNION (" ++ sqlPrettyPrintQuery q2 ++ ")"
| sqlIntersect q1 q2 => "(" ++ sqlPrettyPrintQuery q1 ++ ") INTERSECT (" ++ sqlPrettyPrintQuery q2 ++ ")"
| sqlExcept q1 q2 => "(" ++ sqlPrettyPrintQuery q1 ++ ") EXCEPT (" ++ sqlPrettyPrintQuery q2 ++ ")"
end

with sqlPrettyPrintTableExpr (t: sqlTableExpression): string := match t with
| sqlTable id => "`" ++ id ++ "`"
| sqlCrossProduct t1 t2 => "(" ++ sqlPrettyPrintTableExpr t1 ++ "), (" ++ sqlPrettyPrintTableExpr t2 ++ ")"
| sqlTableFromQuery q => "(" ++ sqlPrettyPrintQuery q ++ ")"
end.

Definition prettyPrintSqlSystem (sys: sqlSystem): string := match sys with
| (sqlSig, sqlThy) =>
       (concat "; " (map sqlPrettyPrintDecl sqlSig))
    ++ ";;;;"
    ++ (concat "; " (map sqlPrettyPrintQuery sqlThy))
end.

