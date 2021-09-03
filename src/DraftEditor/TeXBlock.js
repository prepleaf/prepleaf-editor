import React from 'react';
import katex from 'katex';
import 'katex/dist/katex.css';

export class KatexOutput extends React.Component {
	constructor(props) {
		super(props);
		this._timer = null;
	}

	_update() {
		if (this._timer) {
			clearTimeout(this._timer);
		}

		this._timer = setTimeout(() => {
			katex.render(this.props.content, this.containerRef, {
				displayMode: true,
			});
		}, 0);
	}

	componentDidMount() {
		this._update();
	}

	componentWillReceiveProps(nextProps) {
		if (nextProps.content !== this.props.content) {
			this._update();
		}
	}

	componentWillUnmount() {
		clearTimeout(this._timer);
		this._timer = null;
	}

	render() {
		let Component = 'div';
		if (this.props.inline) {
			Component = 'span';
		}
		return (
			<Component
				contentEditable={this.props.contentEditable}
				className={`${this.props.inline ? 'inline-katex-wrapper' : ''}`}
				ref={this.handleContainerRef}
				onClick={this.props.onClick}
			/>
		);
	}
	handleContainerRef = (ref) => {
		this.containerRef = ref;
	};
}

export default class TeXBlock extends React.Component {
	constructor(props) {
		super(props);
		this.state = { editMode: false };

		this._onClick = () => {
			if (this.state.editMode) {
				return;
			}

			this.setState(
				{
					editMode: true,
					texValue: this._getValue(),
				},
				() => {
					this._startEdit();
				}
			);
		};

		this._onValueChange = (evt) => {
			var value = evt.target.value;
			var invalid = false;
			try {
				katex.__parse(value);
			} catch (e) {
				invalid = true;
			} finally {
				this.setState({
					invalidTeX: invalid,
					texValue: value,
				});
			}
		};

		this._save = () => {
			var entityKey = this.props.block.getEntityAt(0);
			var newContentState = this.props.contentState.mergeEntityData(entityKey, {
				content: this.state.texValue,
			});
			this.setState(
				{
					invalidTeX: false,
					editMode: false,
					texValue: null,
				},
				this._finishEdit.bind(this, newContentState)
			);
		};

		this._remove = () => {
			this.props.blockProps.onRemove(this.props.block.getKey());
		};
		this._startEdit = () => {
			this.props.blockProps.onStartEdit(this.props.block.getKey());
		};
		this._finishEdit = (newContentState) => {
			this.props.blockProps.onFinishEdit(
				this.props.block.getKey(),
				newContentState
			);
		};
	}

	_getValue() {
		return this.props.contentState
			.getEntity(this.props.block.getEntityAt(0))
			.getData()['content'];
	}

	render() {
		var texContent = null;
		const { readOnly } = this.props.blockProps;
		if (this.state.editMode) {
			if (this.state.invalidTeX) {
				texContent = '';
			} else {
				texContent = this.state.texValue;
			}
		} else {
			texContent = this._getValue();
		}

		var className = 'TeXEditor-tex';
		if (this.state.editMode) {
			className += ' TeXEditor-activeTeX';
		}

		var editPanel = null;
		if (this.state.editMode) {
			var buttonClass = 'TeXEditor-saveButton';
			if (this.state.invalidTeX) {
				buttonClass += ' TeXEditor-invalidButton';
			}

			editPanel = (
				<div className="TeXEditor-panel">
					<textarea
						className="TeXEditor-texValue"
						onChange={this._onValueChange}
						value={this.state.texValue}
					/>
					<div className="TeXEditor-buttons">
						<button
							className={buttonClass}
							disabled={this.state.invalidTeX}
							onClick={this._save}
						>
							{this.state.invalidTeX ? 'Invalid TeX' : 'Done'}
						</button>
						<button className="TeXEditor-removeButton" onClick={this._remove}>
							Remove
						</button>
					</div>
				</div>
			);
		}

		return (
			<div
				className={className}
				style={{
					cursor: readOnly ? 'default' : '',
				}}
			>
				<KatexOutput
					content={texContent}
					onClick={readOnly ? undefined : this._onClick}
				/>
				{editPanel}
			</div>
		);
	}
}
