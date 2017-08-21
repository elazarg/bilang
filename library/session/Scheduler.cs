//--------------------------------------------------------------------------
// 
//  Copyright (c) Microsoft Corporation.  All rights reserved. 
// 
//  File: LimitedConcurrencyTaskScheduler.cs
//
//--------------------------------------------------------------------------

using System.Collections.Generic;
using System.Linq;

namespace System.Threading.Tasks.Schedulers {

    /* TODO:
     * Change the scheduler to receive direct orders from the controller
     * (controller=policy, scheduler=mechanism)
     * */

    /// <summary>
    /// Provides a task scheduler that ensures a maximum concurrency level while
    /// running on top of the ThreadPool.
    /// </summary>
    public class OrderedTaskScheduler : TaskScheduler {
        int? waitingForMessage = null;

        internal async Task Yield() {
            waitingForMessage = Task.CurrentId;
            await Task.Yield();
        }
        
        /// <summary>The list of tasks to be executed.</summary>
        private readonly LinkedList<Task> _tasks = new LinkedList<Task>(); // protected by lock(_tasks)
        /// <summary>Whether the scheduler is currently processing work items.</summary>
        private bool _delegatesQueuedOrRunning = false; // protected by lock(_tasks)

        /// <summary>Queues a task to the scheduler.</summary>
        /// <param name="task">The task to be queued.</param>
        protected sealed override void QueueTask(Task task) {
            // Add the task to the list of tasks to be processed.  If there aren't enough
            // delegates currently queued or running to process tasks, schedule another.
            lock (_tasks) {
                _tasks.AddLast(task);
                if (!_delegatesQueuedOrRunning) {
                    _delegatesQueuedOrRunning = true;
                    NotifyThreadPoolOfPendingWork();
                }
            }
        }

        /// <summary>
        /// Informs the ThreadPool that there's work to be executed for this scheduler.
        /// </summary>
        private void NotifyThreadPoolOfPendingWork() {
            ThreadPool.UnsafeQueueUserWorkItem(_ => {
                // Process all available items in the queue.
                while (true) {
                    Task item;
                    lock (_tasks) {
                        // When there are no more items to be processed,
                        // note that we're done processing, and get out.
                        if (_tasks.Count == 0) {
                            _delegatesQueuedOrRunning = false;
                            break;
                        }

                        // Get the next item from the queue
                        while (true) {
                            item = _tasks.First.Value;
                            _tasks.RemoveFirst();
                            if (item.Id == waitingForMessage)
                                _tasks.AddLast(item);
                            else
                                break;
                        }
                    }

                    // Execute the task we pulled out of the queue
                    base.TryExecuteTask(item);
                }
            }, null);
        }

        /// <summary>Attempts to execute the specified task on the current thread.</summary>
        /// <param name="task">The task to be executed.</param>
        /// <param name="taskWasPreviouslyQueued"></param>
        /// <returns>Whether the task could be executed on the current thread.</returns>
        protected sealed override bool TryExecuteTaskInline(Task task, bool taskWasPreviouslyQueued) => false;

        /// <summary>Attempts to remove a previously scheduled task from the scheduler.</summary>
        /// <param name="task">The task to be removed.</param>
        /// <returns>Whether the task could be found and removed.</returns>
        protected sealed override bool TryDequeue(Task task) {
            lock (_tasks) return _tasks.Remove(task);
        }

        /// <summary>Gets the maximum concurrency level supported by this scheduler.</summary>
        public sealed override int MaximumConcurrencyLevel { get { return 1; } }

        /// <summary>Gets an enumerable of the tasks currently scheduled on this scheduler.</summary>
        /// <returns>An enumerable of the tasks currently scheduled.</returns>
        protected sealed override IEnumerable<Task> GetScheduledTasks() {
            bool lockTaken = false;
            try {
                Monitor.TryEnter(_tasks, ref lockTaken);
                if (lockTaken) {
                    foreach (var t in _tasks) {
                        if (waitingForMessage != t.Id)
                            yield return t;
                    }
                } else throw new NotSupportedException();
            } finally {
                if (lockTaken) Monitor.Exit(_tasks);
            }
        }
    }
}
