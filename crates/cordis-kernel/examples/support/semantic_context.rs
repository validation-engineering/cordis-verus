use cordis_kernel::mixed_driver::fresh::{Blueprint, Command, Instruction};
use cordis_kernel::Port;

pub fn service() -> Port {
    Port { key: 7, realm: 0 }
}

pub fn own_service() -> Port {
    Port { key: 11, realm: 0 }
}

pub fn bank() -> Vec<Blueprint> {
    vec![
        // A dormant child reserves a service before it publishes anything.
        Blueprint::new(
            vec![],
            vec![Port { key: 13, realm: 0 }],
            vec![Instruction::Unit],
        ),
        Blueprint::new(
            vec![],
            vec![service()],
            vec![Instruction::Provide {
                key: service(),
                value: 7,
                next: None,
            }],
        ),
        Blueprint::new(
            vec![service()],
            vec![own_service()],
            vec![
                Instruction::Xor {
                    key: service(),
                    mask: 5,
                    next: Some(1),
                },
                Instruction::Child {
                    blueprint: 0,
                    next: Some(2),
                },
                Instruction::Provide {
                    key: own_service(),
                    value: 42,
                    next: None,
                },
            ],
        ),
        Blueprint::new(
            vec![service()],
            vec![],
            vec![
                Instruction::Xor {
                    key: service(),
                    mask: 5,
                    next: Some(1),
                },
                Instruction::Child {
                    blueprint: 0,
                    next: None,
                },
            ],
        ),
    ]
}

pub fn setup() -> Vec<Command> {
    vec![
        Command::Insert {
            parent: None,
            blueprint: 1,
        },
        Command::Begin { actor: 0 },
        Command::Step { actor: 0 },
        Command::Insert {
            parent: None,
            blueprint: 2,
        },
        Command::Begin { actor: 1 },
        Command::Step { actor: 1 },
        Command::Step { actor: 1 },
        Command::Step { actor: 1 },
    ]
}

pub fn cleanup() -> Vec<Command> {
    let mut commands = setup();
    commands.extend([
        Command::Retire { actor: 1 },
        Command::Depart { actor: 1 },
        Command::Unload { actor: 1 },
    ]);
    commands
}

pub fn conflicting_retry() -> Vec<Command> {
    let mut commands = cleanup();
    commands.extend([
        Command::Insert {
            parent: None,
            blueprint: 3,
        },
        Command::Begin { actor: 3 },
        Command::Step { actor: 3 },
        Command::Step { actor: 3 },
    ]);
    commands
}
