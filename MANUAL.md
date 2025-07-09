# pql manual

## Quick start

```
documents
| join (
    invoices | project invoice_id = id, invoice_email_id
) on invoice_id
| join kind=inner (
    invoice_emails
    | where like(address_from, '%@example.com')
    | project invoice_email_id = id
) on invoice_email_id
| where isnotnull(deleted_at)
| count
```

### Operators

- Equality and comparison: `==`, `!=`, `<`, `<=`, `>`, `>=`
- Case insensitive string equality: `=~`, `!~`
- `in`: `type in ('DELIVERY_SLIP', 'QUOTE')`
- Arithmetic: `+`, `-`, `/`, `*`, `%`, with their usual meaning.

### Functions

- `iif`/`iff`: `iff(cond, x, y)`, if `cond` is met `x` is chosen, otherwise `y`
- `isnull(x)`: `x IS NULL`
- `isnotnull(x)`: `x IS NOT NULL`
- `not(cond)`: `NOT cond`
- `now()`: `CURRENT_TIMESTAMP`
- `strcat(a, b, ...)`: `a || b || ...`
- `tolower(x)`, `toupper(x)`

Note that any functions unknown to `pql` are passed as-is to the database. For example, the following is valid when using PostgreSQL:
```
documents
| where jsonb_path_query(metadata, '$.items.size() > 10')
```

## A tour of `pql`

To select everything from a table:
```
documents
```
The table name is the starting point of all queries. We'll be using "pipes" to process the data – information flows from top to bottom through each stage of the query delimited by the `|` character.

### `project`

Select a subset of columns:
```
documents
| project document_id, type, created_at
```

Select a subset of columns with different names:
```
documents
| project ID = document_id, Type = type, CreatedAt = created_at
```

Create columns using available columns & functions:
```
documents
| project age = now - created_at, is_deleted = isnotnull(deleted_at)
```

All of the above can be mixed and matched. Subsequent stages of the pipeline will only see the columns retrieved by `project`.

### `extend`

Add new columns to the already selected ones:
```
documents
| extend age = now - created_at
```
This will retrieve all columns from `documents` plus the column `age`.

Unlike with `project` a column name is not required:
```
documents
| extend now - created_at
```
The name of the column will be literally the text `now - created_at`.

`extend` can only use columns which are in its scope
```
documents
| project id, type, format
| extend is_image = format == 'IMAGE'
```
In this case the `extend` stage above can use only what `project` selects above. It can't use `created_at`, for example.

### `where`

- Alias: `filter`

Select a subset of rows:
```
documents
| where type == 'DELIVERY_SLIP'
```

### `join`

### `as`

Alias a table for the next stage of the pipeline:
```
documents
| as d
```

The alias can be used only in the stage immediately following the alias in the pipeline. In other words, this will not work:
```
documents
| as d
| where d.created_at > '2024-01-01'
| project d.document_id;
```
The `project` stage will fail as the alias `d` is not available anymore.

### `order`

- Alias: `sort`

### `limit`

- Alias: `take`

### `top`

- Equivalent to `order` + `limit`

### `count`

### `summarize`

### `render`

### Macros