// This file is part of Gear.

// Copyright (C) 2021-2022 Gear Technologies Inc.
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

use core::convert::TryInto;

use crate::{
    manager::ExtManager, Config, CostsPerBlockOf, DispatchStashOf, Event, GasHandlerOf, Pallet,
    QueueOf,
};
use alloc::string::ToString;
use common::{
    event::{
        MessageWokenRuntimeReason, MessageWokenSystemReason, RuntimeReason, SystemReason,
        UserMessageReadSystemReason,
    },
    scheduler::*,
    storage::*,
    GasTree, Origin,
};
use core_processor::common::ActorExecutionErrorReason;
use gear_core::{
    ids::{CodeId, MessageId, ProgramId, ReservationId},
    message::ReplyMessage,
};
use sp_runtime::Saturating;

impl<T: Config> TaskHandler<T::AccountId> for ExtManager<T>
where
    T::AccountId: Origin,
{
    fn pause_program(&mut self, _program_id: ProgramId) {
        todo!("#646");
    }

    fn remove_code(&mut self, _code_id: CodeId) {
        todo!("#646");
    }

    fn remove_from_mailbox(&mut self, user_id: T::AccountId, message_id: MessageId) {
        // Read reason.
        let reason = UserMessageReadSystemReason::OutOfRent.into_reason();

        // Reading message from mailbox.
        let mailboxed = Pallet::<T>::read_message(user_id, message_id, reason)
            .unwrap_or_else(|| unreachable!("Scheduling logic invalidated!"));

        // TODO: consider send signal to program itself (#1742)

        // Consuming gas handler for mailboxed message.
        Pallet::<T>::consume_and_retrieve(mailboxed.id());
    }

    fn remove_from_waitlist(&mut self, program_id: ProgramId, message_id: MessageId) {
        // Wake reason.
        let reason = MessageWokenSystemReason::OutOfRent.into_reason();

        // Waking dispatch.
        let waitlisted = Pallet::<T>::wake_dispatch(program_id, message_id, reason)
            .unwrap_or_else(|| unreachable!("Scheduling logic invalidated!"));

        self.send_signal(message_id, waitlisted.destination());

        // Trap explanation.
        let trap = ActorExecutionErrorReason::OutOfRent;

        // Generate trap reply.
        if self.check_program_id(&waitlisted.source()) {
            // TODO: consider wether alert `waitlisted.source()` and how (#1741)
        } else {
            // Sending trap reply to user, by depositing event.
            //
            // There is no reason to use `Pallet::<T>::send_user_message( .. )`,
            // because there is no need in reply in future, so no reason
            // and funds to pay mailbox rent for it.

            // Note: for users, trap replies always contain
            // string explanation of the error.
            let trap = trap
                .to_string()
                .into_bytes()
                .try_into()
                .expect("Error message is too large");

            // Creating reply message.
            //
            // # Safety
            //
            // 1. The dispatch.id() has already been checked
            // 2. This reply message is generated by our system
            //
            // So, the message id of this reply message will not be duplicated.
            let trap_reply =
                ReplyMessage::system(message_id, trap, core_processor::ERR_STATUS_CODE)
                    .into_stored(program_id, waitlisted.source(), message_id);

            // Depositing appropriate event.
            Pallet::<T>::deposit_event(Event::UserMessageSent {
                message: trap_reply,
                expiration: None,
            });
        }

        // Consuming gas handler for waitlisted message.
        Pallet::<T>::consume_and_retrieve(waitlisted.id());
    }

    fn remove_paused_program(&mut self, _program_id: ProgramId) {
        todo!("#646");
    }

    fn wake_message(&mut self, program_id: ProgramId, message_id: MessageId) {
        if let Some(dispatch) = Pallet::<T>::wake_dispatch(
            program_id,
            message_id,
            MessageWokenRuntimeReason::WakeCalled.into_reason(),
        ) {
            QueueOf::<T>::queue(dispatch)
                .unwrap_or_else(|e| unreachable!("Message queue corrupted! {:?}", e));
        }
    }

    fn send_dispatch(&mut self, stashed_message_id: MessageId) {
        // No validation required. If program doesn't exist, then NotExecuted appears.

        let (dispatch, stored_bn) = DispatchStashOf::<T>::take(stashed_message_id)
            .unwrap_or_else(|| unreachable!("Scheduler & Stash logic invalidated!"));

        // Unlocking gas for delayed sending rent payment.
        GasHandlerOf::<T>::unlock_all(dispatch.id())
            .unwrap_or_else(|e| unreachable!("GasTree corrupted! {:?}", e));

        // Charging locked gas for holding in dispatch stash
        // Charge gas for message save
        let current_bn = Pallet::<T>::block_number();
        let hold_interval = Interval {
            start: stored_bn.start,
            finish: current_bn,
        };
        Pallet::<T>::charge_for_hold(
            dispatch.id(),
            hold_interval,
            CostsPerBlockOf::<T>::dispatch_stash(),
        );

        QueueOf::<T>::queue(dispatch)
            .unwrap_or_else(|e| unreachable!("Message queue corrupted! {:?}", e));
    }

    fn send_user_message(&mut self, stashed_message_id: MessageId, to_mailbox: bool) {
        // TODO: validate here destination and send error reply, if required.
        // Atm despite the fact that program may exist, message goes into mailbox / event.
        let (message, stored_bn) = DispatchStashOf::<T>::take(stashed_message_id)
            .map(|(dispatch, bn)| (dispatch.into_parts().1, bn))
            .unwrap_or_else(|| unreachable!("Scheduler & Stash logic invalidated!"));

        // Unlocking gas for delayed sending rent payment.
        GasHandlerOf::<T>::unlock_all(message.id())
            .unwrap_or_else(|e| unreachable!("GasTree corrupted! {:?}", e));

        // Charge gas for message save
        let current_bn = Pallet::<T>::block_number();
        let hold_interval = Interval {
            start: stored_bn
                .start
                .saturating_sub(CostsPerBlockOf::<T>::reserve_for()),
            finish: current_bn,
        };
        Pallet::<T>::charge_for_hold(
            message.id(),
            hold_interval,
            CostsPerBlockOf::<T>::dispatch_stash(),
        );

        Pallet::<T>::send_user_message_after_delay(message, to_mailbox);
    }

    fn remove_gas_reservation(&mut self, program_id: ProgramId, reservation_id: ReservationId) {
        let _slot = Self::remove_gas_reservation_impl(program_id, reservation_id);
    }
}
