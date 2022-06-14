export const MISSING_KEY = '___MISSING_KEY___'
export const MISSING_TABLE_SERVICE = '___MISSING_TABLE_SERVICE___'

export type Table<T> = Readonly<Record<string, Readonly<T>>>

export type TableService<T> = {
    get(key: string): Promise<T>;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
}


// Q 2.1 (a)
export function makeTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>): TableService<T> {
    // optional initialization code
    return {
        get(key: string): Promise<T> {
            return new Promise <T> ((resolve, reject) => {
                return sync().then((table) => {
                    if (key in table)
                        resolve(table[key]);
                    else
                        reject(MISSING_KEY);                     
                   })
                   .catch(() => reject(MISSING_KEY))
            })
         },
        set(key: string, val: T): Promise<void> {
            return new Promise<void>((resolve, reject) => {
                return sync().then((table) => {
                    let newTable : Record<string, Readonly<T>> = {};
                    for (let k in table){
                        if(k !== key){
                            newTable[key] = table[key];
                        }
                    }
                    newTable[key] = val;
                    sync(newTable).then(() => resolve())
                    .catch(() => reject(MISSING_KEY));
                })
                .catch(() => reject(MISSING_KEY));
            })
        },
        delete(key: string): Promise<void> {
            return new Promise<void>((resolve, reject) => {
                return sync().then((table) => {
                    let newTable : Record<string, Readonly<T>> = {};
                    let isInTable : boolean = false;
                    for (let k in table) {
                        if(k !== key) {
                            newTable[key] = table[key];
                        }
                        else {
                            isInTable = true;
                        }
                    }
                    if(!isInTable) {
                        reject(MISSING_KEY);
                    }
                    else{
                        sync(newTable).then(() => resolve())
                        .catch(() => reject(MISSING_KEY));
                    }
                })
                .catch(() => reject(MISSING_KEY));
            })
        }
    }
}

// Q 2.1 (b)
export function getAll<T>(store: TableService<T>, keys: string[]): Promise<T[]> {
    let values = [];
    for (let i = 0; i < keys.length; i++) {
        values[i] = store.get(keys[i]);
    }
    return Promise.all(values);
}


// Q 2.2
export type Reference = { table: string, key: string }

export type TableServiceTable = Table<TableService<object>>

export function isReference<T>(obj: T | Reference): obj is Reference {
    return typeof obj === 'object' && 'table' in obj
}

export async function constructObjectFromTables(tables: TableServiceTable, ref: Reference) {

    async function deref(ref: Reference) {
        if (ref.table in tables) {
            try {
                let value = await tables[ref.table].get(ref.key);
                let newEntries : any[] = await Promise.all(Object.entries(value).map(
                    async(entry) => {
                        if (isReference(entry[1])) {
                            return [entry[0], await deref(entry[1])];
                        }
                        else {
                            return entry;
                        }
                    }
                ))
                return Object.fromEntries(newEntries);
            }
            catch {
                return Promise.reject(MISSING_KEY);
            }
        }
        else {
            return Promise.reject(MISSING_TABLE_SERVICE);
        }
    }

    return deref(ref)
}

// Q 2.3

export function lazyProduct<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        for (let v1 of g1()) {
            for (let v2 of g2()) {
                yield [v1, v2];
            }
        }
    }
}

export function lazyZip<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        const gen = g2();
        for (let v1 of g1()) {
            yield [v1, gen.next().value];
        }
    }
}

// Q 2.4
export type ReactiveTableService<T> = {
    get(key: string): T;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
    subscribe(observer: (table: Table<T>) => void): void
}

export async function makeReactiveTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>, optimistic: boolean): Promise<ReactiveTableService<T>> {
    // optional initialization code

    let _table: Table<T> = await sync();
    let currObserver = function (x: any) {};
    let observers : Function[] = [];

    const handleMutation = async (newTable: Table<T>) => {
        if (optimistic) {
            for (let i = 0; i < observers.length; i++) {
                observers[i](newTable);
            }
        }
        try {
            _table = await sync(newTable);
        } catch (error) {
            handleMutation(_table);
            Promise.reject(error);
        }
    }
    return {
        get(key: string): T {
            if (key in _table) {
                return _table[key]
            } else {
                throw MISSING_KEY
            }
        },
        async set(key: string, val: T): Promise<void> {
            let newTable : Record<string, Readonly<T>> = {};
            for (let k in _table) {
                if (k !== key) {
                    newTable[k] = _table[k];
                }
            }
            newTable[key] = val;
            try {
                await handleMutation(newTable);
            } catch (error) {
                currObserver(_table);
                await Promise.reject(error);
            }
            if (!optimistic) {
                currObserver(newTable);
            }
        },
        async delete(key: string): Promise<void> {
            let newTable : Record<string, Readonly<T>> = {};
            if (key in _table) {
                for (let k in _table) {
                    if (k !== key) {
                        newTable[k] = _table[k];
                    }
                }
            }
            else {
                Promise.reject(MISSING_KEY);
            }
            try {
                await handleMutation(newTable);
            } catch (error) {
                currObserver(_table);
                await Promise.reject(error);
            }
            if (!optimistic) {
                currObserver(newTable);
            }
        },
        subscribe(observer: (table: Table<T>) => void): void {
            currObserver = observer;
            observers.push(currObserver);
        }
    }
}