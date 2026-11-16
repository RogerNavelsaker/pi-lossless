import { DatabaseSync } from "node:sqlite";

export class Database extends DatabaseSync {
  constructor(path, options = {}) {
    super(path, options.readonly ? { readOnly: true } : {});
  }

  query(sql) {
    return this.prepare(sql);
  }
}
