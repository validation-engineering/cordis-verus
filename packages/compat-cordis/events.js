// Adapted from Cordis f8ea3cd50f1a5724e8e715995bcde131c9c12b2c.
// Copyright (c) 2021-present Shigma. MIT; see LICENSE.upstream.
import { defineProperty } from './support.js';
import { Context } from './context.js';
import { Fiber, FiberState } from './fiber.js';
import { DisposableList, symbols } from './utils.js';
const defaultUpdateDispatchers = new WeakSet();
export function isBailed(value) {
    return value !== null && value !== false && value !== undefined;
}
export class EventsService {
    ctx;
    _hooks = Object.create(null);
    constructor(ctx){
        this.ctx = ctx;
        defineProperty(this, symbols.tracker, {
            property: 'ctx',
            noShadow: true
        });
        this.on('internal/listener', function(name, listener, options) {
            if (name === 'internal/update' && !options.global) {
                const hooks = this.fiber._hooks['internal/update'] ??= new DisposableList();
                const method = options.prepend ? 'unshift' : 'push';
                return hooks[method](listener);
            }
        });
        this.on('internal/update', function(config, noSave, next) {
            const cbs = [
                ...this._hooks['internal/update'] || []
            ];
            const _next = ()=>{
                const cb = cbs.shift();
                if (!cb) return next();
                return this.ctx.fiber._domain.invokeEvent(this.ctx.fiber, cb, this, [config, noSave, _next], true);
            };
            return _next();
        }, {
            global: true,
            prepend: true
        });
        // Record this exact built-in entry, not a listener count. An unknown
        // listener must disable automatic coordination without invoking filters.
        defaultUpdateDispatchers.add(this._hooks['internal/update'][0]);
    }
    hasUpdateObservers(fiber) {
        return !!fiber._hooks['internal/update']?.length
            || (this._hooks['internal/update'] || []).some(hook => !defaultUpdateDispatchers.has(hook));
    }
    _resolve(type, args) {
        const thisArg = typeof args[0] === 'object' || typeof args[0] === 'function' ? args.shift() : null;
        const name = args.shift();
        if ((typeof name !== 'string' || !name.startsWith('internal/')) && this._hooks['internal/dispatch']?.length) {
            this.emit('internal/dispatch', type, name, args, thisArg);
        }
        const filter = thisArg?.[Context.filter];
        return [
            thisArg,
            (this._hooks[name] || []).filter((hook)=>hook.global || !filter || filter.call(thisArg, hook.ctx)).map((hook)=>function(...values) {
                return hook.ctx.fiber._domain.invokeEvent(hook.ctx.fiber, hook.callback, this, values, type === 'waterfall');
            })
        ];
    }
    dispatch(type, args) {
        const [thisArg, callbacks] = this._resolve(type, args);
        return callbacks.map((callback)=>callback.bind(thisArg));
    }
    async parallel(...args) {
        const [thisArg, callbacks] = this._resolve('emit', args);
        const results = await Promise.allSettled(callbacks.map(async (callback)=>Reflect.apply(callback, thisArg, args)));
        const errors = results.filter((result)=>result.status === 'rejected');
        if (errors.length) throw new AggregateError(errors.map((error)=>error.reason));
    }
    emit(...args) {
        const [thisArg, callbacks] = this._resolve('emit', args);
        for (const callback of callbacks)Reflect.apply(callback, thisArg, args);
    }
    async serial(...args) {
        const [thisArg, callbacks] = this._resolve('serial', args);
        for (const callback of callbacks){
            const result = await Reflect.apply(callback, thisArg, args);
            if (isBailed(result)) return result;
        }
    }
    bail(...args) {
        const [thisArg, callbacks] = this._resolve('bail', args);
        for (const callback of callbacks){
            const result = Reflect.apply(callback, thisArg, args);
            if (isBailed(result)) return result;
        }
    }
    waterfall(...args) {
        const [thisArg, callbacks] = this._resolve('waterfall', args);
        const inner = args.pop();
        const dispatch = ()=>{
            const callback = callbacks.shift();
            if (!callback) return inner();
            let called = false;
            const next = ()=>{
                if (called) throw new Error('next() called multiple times');
                called = true;
                return dispatch();
            };
            return Reflect.apply(callback, thisArg, [
                ...args,
                next
            ]);
        };
        return dispatch();
    }
    register(label, name, callback, options) {
        const method = options.prepend ? 'unshift' : 'push';
        return this.ctx.fiber.effect(()=>{
            const hooks = this._hooks[name] ??= [];
            hooks[method]({
                ctx: this.ctx,
                callback,
                ...options
            });
            return ()=>this.unregister(name, callback);
        }, label);
    }
    unregister(name, callback) {
        const hooks = this._hooks[name];
        if (!hooks) return;
        const index = hooks.findIndex((hook)=>hook.callback === callback);
        if (index >= 0) {
            hooks.splice(index, 1);
            if (!hooks.length) delete this._hooks[name];
            return true;
        }
    }
    on(name, listener, options) {
        if (typeof options !== 'object') {
            options = {
                prepend: options
            };
        }
        this.ctx.fiber.assertActive();
        listener = this.ctx.reflect.bind(listener);
        const result = this.bail(this.ctx, 'internal/listener', name, listener, options);
        if (result) return result;
        const label = `ctx.on(${typeof name === 'string' ? JSON.stringify(name) : name.toString()})`;
        return this.register(label, name, listener, options);
    }
    once(name, listener, options) {
        const dispose = this.on(name, function(...args) {
            dispose();
            return listener.apply(this, args);
        }, options);
        return dispose;
    }
}
