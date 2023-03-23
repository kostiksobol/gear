// This file is part of Gear.

// Copyright (C) 2022 Gear Technologies Inc.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Module for messenger implementation.
//!
//! Messenger provides API for all available gear message storing.

use crate::storage::{
    Counted, CountedByKey, Counter, DequeueError, Interval, IterableByKeyMap, IterableMap, Mailbox,
    MailboxError, MapStorage, Queue, Toggler, Waitlist, WaitlistError,
};
use core::fmt::Debug;

/// Represents messenger's logic of centralized message processing behavior.
pub trait Messenger {
    /// Block number type of the messenger.
    type BlockNumber;
    /// Capacity of the messenger.
    ///
    /// This type defines length type of the queue, sent and
    /// dequeued messages within same block amount type.
    type Capacity;
    /// Inner error type generated by gear's storage types.
    type Error: Debug + DequeueError + MailboxError + WaitlistError;
    /// Output error of each storage algorithm.
    ///
    /// Implements `From<Self::Error>` to be able to return
    /// any required error type.
    type OutputError: From<Self::Error> + Debug;

    /// First key of the mailbox storage.
    ///
    /// Present to clarify compiler behavior over associated types.
    type MailboxFirstKey;
    /// Second key of the mailbox storage.
    ///
    /// Present to clarify compiler behavior over associated types.
    type MailboxSecondKey;
    /// Stored values type for `Self::Mailbox`.
    ///
    /// Present to clarify compiler behavior over associated types.
    type MailboxedMessage;
    /// Stored values type for `Self::Queue`.
    ///
    /// Present to clarify compiler behavior over associated types.
    type QueuedDispatch;
    /// First key of the waitlist storage.
    ///
    /// Present to clarify compiler behavior over associated types.
    type WaitlistFirstKey;
    /// Second key of the waitlist storage.
    ///
    /// Present to clarify compiler behavior over associated types.
    type WaitlistSecondKey;
    /// Stored values type for `Self::Waitlist`.
    ///
    /// Present to clarify compiler behavior over associated types.
    type WaitlistedMessage;
    /// Key for value types for `Self::DispatchStash`.
    ///
    /// Present to clarify compiler behavior over associated types.
    type DispatchStashKey;

    /// Amount of messages sent from outside (from users)
    /// within the current block.
    ///
    /// Used as local counter for `MessageId` generation.
    type Sent: Counter<Value = Self::Capacity>;

    /// Amount of messages dequeued with the current block.
    ///
    /// Used for depositing informational event about how much messages
    /// were took from queue in `process_queue` execution.
    type Dequeued: Counter<Value = Self::Capacity>;

    /// Allowance of queue processing.
    ///
    /// Used for checking could `process_queue` continue it's execution.
    /// Execution finishes, once message requeued at the end of the queue,
    /// because it alerts, that this execution exceed gas allowance of the
    /// current block by gear's processing algorithm.
    type QueueProcessing: Toggler;

    /// Gear message queue.
    ///
    /// Message queue contains only messages addressed to programs.
    /// Messages from queue process on idle of each block in `process_queue`,
    /// function, except case of runtime upgrade - then processing skipped.
    type Queue: Queue<Value = Self::QueuedDispatch, Error = Self::Error, OutputError = Self::OutputError>
        + Counted<Length = Self::Capacity>
        + IterableMap<Result<Self::QueuedDispatch, Self::OutputError>>;

    /// Gear mailbox.
    ///
    /// Mailbox contains only messages addressed to user accounts.
    /// Any address meant as user account if it's not program id.
    ///
    /// Only mailbox owner (user with message's destination address)
    /// can claim value from the message, removing it afterward, or claim
    /// and send reply on received message, if it still present (#642).
    type Mailbox: Mailbox<
            Key1 = Self::MailboxFirstKey,
            Key2 = Self::MailboxSecondKey,
            Value = Self::MailboxedMessage,
            BlockNumber = Self::BlockNumber,
            Error = Self::Error,
            OutputError = Self::OutputError,
        > + CountedByKey<Key = Self::MailboxFirstKey, Length = usize>
        + IterableMap<(Self::MailboxedMessage, Interval<Self::BlockNumber>)>
        + IterableByKeyMap<
            (Self::MailboxedMessage, Interval<Self::BlockNumber>),
            Key = Self::MailboxFirstKey,
        >;

    /// Gear waitlist.
    ///
    /// Waitlist contains messages, which execution should be
    /// delayed for some logic.
    ///
    /// Message can be inserted into waitlist only in these cases:
    /// 1. Destination program called `gr_wait` while was executing
    /// this message, so only this program can remove and
    /// requeue it by `gr_wake` call in any execution.
    /// 2. The message sent to program, that hadn't finished its
    /// initialization, and will be automatically removed once
    /// result of initialization would be available.
    /// 3. Restored after resuming paused programs. On pause we
    /// collect waitlist content addressed to the program,
    /// removing it afterwards. On resume, user should provide
    /// the same content to be able to unpause program, which
    /// gonna be added into waitlist again.
    ///
    /// More cases may be considered in future.
    ///
    /// Gear runtime also charges rent for holding in waitlist.
    /// Note, that system can remove message from waitlist,
    /// if it couldn't pay rent for holding there further.
    /// For details, see `pallet-gear-scheduler`.
    type Waitlist: Waitlist<
            Key1 = Self::WaitlistFirstKey,
            Key2 = Self::WaitlistSecondKey,
            Value = Self::WaitlistedMessage,
            BlockNumber = Self::BlockNumber,
            Error = Self::Error,
            OutputError = Self::OutputError,
        > + CountedByKey<Key = Self::WaitlistFirstKey, Length = usize>
        + IterableMap<(Self::WaitlistedMessage, Interval<Self::BlockNumber>)>
        + IterableByKeyMap<
            (Self::WaitlistedMessage, Interval<Self::BlockNumber>),
            Key = Self::WaitlistFirstKey,
        >;

    type DispatchStash: MapStorage<
        Key = Self::DispatchStashKey,
        Value = (Self::QueuedDispatch, Interval<Self::BlockNumber>),
    >;

    /// Resets all related to messenger storages.
    ///
    /// It's a temporary production solution to avoid DB migrations
    /// and would be available for test purposes only in the future.
    fn reset() {
        Self::Sent::reset();
        Self::Dequeued::reset();
        Self::QueueProcessing::allow();
        Self::Queue::clear();
        Self::Mailbox::clear();
        Self::Waitlist::clear();
        Self::DispatchStash::clear();
    }
}
