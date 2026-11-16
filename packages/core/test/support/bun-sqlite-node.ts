import { DatabaseSync, type StatementSync } from "node:sqlite";

export type Statement = StatementSync;

export class Database extends DatabaseSync {
  constructor(path: string, options: { readonly?: boolean } = {}) {
    super(path, options.readonly ? { readOnly: true } : {});
  }

  query(sql: string): StatementSync {
    return this.prepare(sql);
  }
}
